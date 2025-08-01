// RUN: %parallel-boogie -extractLoops "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK-L: Boogie program verifier finished with 2 verified, 0 errors

procedure {:entrypoint} simple_irreducible() {
    var x: int;
    x := 0;
    A:
        assume x == 0;
        x := x + 1;
        goto B, C;

    B:
        assume x <= 2;
        x := x - 1;
        goto C, D;
    C: 
        x := x + 1;
        goto B;
    D: 
        assume x <= 1;
}