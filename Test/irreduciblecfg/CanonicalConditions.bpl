// RUN: %parallel-boogie "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK-L: Boogie program verifier finished with 1 verified, 0 errors

procedure simple_irreducible() {
    var x: int;
    x := 0;
    A:
        assert x == 0;
        x := x + 1;
        goto B, C;

    B:
        assert x <= 2;
        x := x - 1;
        goto C, D;
    C: 
        x := x + 1;
        goto B;
    D: 
        assert x <= 1;
}