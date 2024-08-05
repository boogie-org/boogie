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

atomic action {:layer 1} B({:linear_in} m: Map int int, i: int, j: int)
asserts Map_Contains(m, i);
asserts !Map_Contains(m, j);
{
    var {:linear} s: Set int;
    var x: [int]int;
    var y: [int]int;
    var {:linear} m': Map int int;

    call s, x := Map_Unpack(m);
    assert Set_Contains(s, i);
    x[j] := 42;
    call m' := Map_Pack(s, x);
    assert m == m';
}

var {:linear} g: Map int int;

atomic action {:layer 1} C(i: int, j: int)
modifies g;
asserts Map_Contains(g, i);
asserts !Map_Contains(g, j);
{
    var {:linear} s: Set int;
    var x: [int]int;
    var y: [int]int;
    var m': Map int int;

    m' := g;
    call s, x := Map_Unpack(g);
    assert Set_Contains(s, i);
    x[j] := 42;
    call g := Map_Pack(s, x);
    assert g == m';
}