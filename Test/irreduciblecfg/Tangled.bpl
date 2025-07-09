// RUN: %parallel-boogie "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK-L: Boogie program verifier finished with 1 verified, 0 errors

var x, y, z : int;
var add: int;
procedure tangled()
    requires x > 0;
    requires y > 0;
    requires z > 0;
    modifies x;
    modifies y;
    modifies z;
    modifies add;
    ensures (x + y + z) == old(x) + old(y) + old(z) + add - old(add);
{
    A: 
        goto B, C;
    B:
        assert (x + y + z) == old(x) + old(y) + old(z) + add - old(add);
        z := z - 1;
        x := x + 1;
        goto C, D, F, EXIT; 
    C: 
        x := x - 1;
        y := y + 1;
        goto B, D, E, EXIT;
    D: 
        assert (x + y + z) == old(x) + old(y) + old(z) + add - old(add);
        y := y + 1;
        add := add + 1;
        goto E, F, D, G;
    E: 
        assert (x + y + z) == old(x) + old(y) + old(z) + add - old(add);
        z := z + 1;
        add := add + 1;
        goto E, F, D, B;
    F: 
        assert (x + y + z) == old(x) + old(y) + old(z) + add - old(add);
        x := x + 1;
        add := add + 1;
        goto E, F, D, C;
    G: 
        z := z + 1;
        y := y - 1;
        goto B, D, EXIT;

    EXIT: 
}