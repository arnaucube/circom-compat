template Multiplier() {
    signal input a; // 3
    signal input b; // 3
    signal input c; // 3
    signal temp;
    signal output d; // 27
    signal output e; // 9

    temp <== a*b;
    d <== temp*c;
    e <== b*c;
}

component main{public [a, b]} = Multiplier();

