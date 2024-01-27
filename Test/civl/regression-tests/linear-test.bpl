// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "A"} A = int;

yield procedure {:layer 1} foo1({:linear "A"} x: int, {:linear "A"} y: int)
{
    assert {:layer 1} x != y;
}

yield procedure {:layer 1} foo3({:layer 1} {:linear_in} x: Lset int, i: [int]bool) returns ({:layer 1} y: Lset int)
requires {:layer 1} IsSubset(i, x->dom);
{
    var {:layer 1} v: Lset int;
    y := x;
    call {:layer 1} v := Lset_Get(y, i);
    assert {:layer 1} IsDisjoint(y->dom, i);
}