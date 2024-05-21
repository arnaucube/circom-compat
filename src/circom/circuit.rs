use std::collections::HashMap;

use ark_ff::PrimeField;
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystemRef, LinearCombination, SynthesisError, Variable,
};

use color_eyre::Result;

use super::R1CS;

/// `self.public_inputs_indexes` stores already allocated public variables. We assume that:
///      1. `self.public_inputs_indexes` is sorted in the same order as circom's r1cs public inputs
///      2. the first element of `self.public_inputs_indexes` is the first element *after* the last non-allocated yet public input
/// example:
///      if circom public values are [1, out1, out2, in1, in2] (where out and in denote public signals only)
///      and `self.public_inputs_indexes` is [Variable(2), Variable(3)]
///      then we will allocate Variable(1), Variable(out1), Variable(out2) and consider that
///      Variable(in1) and Variable(in2) are already allocated as Variable(2), Variable(3)
#[derive(Clone, Debug)]
pub struct CircomCircuit<F: PrimeField> {
    pub r1cs: R1CS<F>,
    pub witness: Option<Vec<F>>,
    pub public_inputs_indexes: Vec<Variable>,
    pub allocate_inputs_as_witnesses: bool,
}

impl<F: PrimeField> CircomCircuit<F> {
    pub fn get_public_inputs(&self) -> Option<Vec<F>> {
        match &self.witness {
            None => None,
            Some(w) => match &self.r1cs.wire_mapping {
                None => Some(w[1..self.r1cs.num_inputs].to_vec()),
                Some(m) => Some(m[1..self.r1cs.num_inputs].iter().map(|i| w[*i]).collect()),
            },
        }
    }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for CircomCircuit<F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        let witness = &self.witness;
        let wire_mapping = &self.r1cs.wire_mapping;

        // Since our cs might already have allocated constraints,
        // We store a mapping between circom's defined indexes and the newly obtained cs indexes
        let mut circom_index_to_cs_index = HashMap::new();
        let n_non_allocated_inputs = self.r1cs.num_inputs - self.public_inputs_indexes.len();

        // allocate non-allocated inputs and update mapping
        for circom_public_input_index in 0..n_non_allocated_inputs {
            if circom_public_input_index == 0 {
                circom_index_to_cs_index.insert(circom_public_input_index, Variable::One);
                continue;
            }

            let variable = match self.allocate_inputs_as_witnesses {
                true => {
                    let witness_var = Variable::Witness(cs.num_witness_variables());
                    cs.new_witness_variable(|| {
                        Ok(match witness {
                            None => F::from(1u32),
                            Some(w) => match wire_mapping {
                                Some(m) => w[m[circom_public_input_index]],
                                None => w[circom_public_input_index],
                            },
                        })
                    })?;
                    witness_var
                }
                false => {
                    let instance_var = Variable::Instance(cs.num_instance_variables());
                    cs.new_input_variable(|| {
                        Ok(match witness {
                            None => F::from(1u32),
                            Some(w) => match wire_mapping {
                                Some(m) => w[m[circom_public_input_index]],
                                None => w[circom_public_input_index],
                            },
                        })
                    })?;
                    instance_var
                }
            };
            circom_index_to_cs_index.insert(circom_public_input_index, variable);
        }

        for circom_public_input_index in n_non_allocated_inputs..self.r1cs.num_inputs {
            let access_input_index = circom_public_input_index - n_non_allocated_inputs;
            circom_index_to_cs_index.insert(
                circom_public_input_index,
                self.public_inputs_indexes[access_input_index],
            );
        }

        for i in 0..self.r1cs.num_aux {
            let circom_defined_r1cs_index = i + self.r1cs.num_inputs;
            circom_index_to_cs_index.insert(
                circom_defined_r1cs_index,
                Variable::Witness(cs.num_witness_variables()),
            );
            cs.new_witness_variable(|| {
                Ok(match witness {
                    None => F::from(1u32),
                    Some(w) => match wire_mapping {
                        Some(m) => w[m[i + self.r1cs.num_inputs]],
                        None => w[circom_defined_r1cs_index],
                    },
                })
            })?;
        }

        let make_index = |index| {
            let new_index = match circom_index_to_cs_index.get(&index) {
                Some(i) => Ok(*i),
                None => Err(SynthesisError::AssignmentMissing),
            };
            Ok(new_index?)
        };

        let make_lc = |lc_data: &[(usize, F)]| {
            lc_data.iter().try_fold(
                LinearCombination::<F>::zero(),
                |lc: LinearCombination<F>, (index, coeff)| {
                    let r1cs_index = make_index(*index);
                    match r1cs_index {
                        Ok(r1cs_index) => Ok(lc + (*coeff, r1cs_index)),
                        Err(e) => Err(e),
                    }
                },
            )
        };

        for constraint in self.r1cs.constraints.iter() {
            let a = make_lc(&constraint.0)?;
            let b = make_lc(&constraint.1)?;
            let c = make_lc(&constraint.2)?;
            let res = cs.enforce_constraint(a, b, c);
            res?
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CircomBuilder, CircomConfig};
    use ark_bn254::Fr;
    use ark_relations::r1cs::ConstraintSystem;

    #[test]
    fn satisfied() {
        let cfg = CircomConfig::<Fr>::new(
            "./test-vectors/mycircuit.wasm",
            "./test-vectors/mycircuit.r1cs",
        )
        .unwrap();
        let mut builder = CircomBuilder::new(cfg);
        builder.push_input("a", 3);
        builder.push_input("b", 11);

        let circom = builder.build().unwrap();
        let cs = ConstraintSystem::<Fr>::new_ref();
        circom.generate_constraints(cs.clone()).unwrap();
        assert!(cs.is_satisfied().unwrap());
    }
}
