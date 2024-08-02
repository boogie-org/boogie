// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

atomic action {:layer 1} A({:linear_in} m: Map int int, s: Set int, i: int)
asserts Set_Contains(s, i);
asserts Set_IsSubset(s, m->dom);
{
    var {:linear} x: Map int int;
    var {:linear} y: Map int int;
    var v: int;

    v := Map_At(m, i);
    x := m;
    call y := Map_Split(x, s);
    assert Map_At(y, i) == v;
    assert !Map_Contains(x, i);
    call Map_Join(x, y);
    assert Map_Contains(x, i);
    assert Map_At(x, i) == v;
}