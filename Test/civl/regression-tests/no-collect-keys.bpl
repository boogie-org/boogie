// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:linear "no_collect_keys"} {:layer 0,1} g: Map int int;
var {:linear} {:layer 0,1} h: Map int int;

atomic action {:layer 1} A()
modifies g, h;
{
    var {:linear} l: Map int int;
    var {:linear "no_collect_keys"} m: Map int int;
    l := h;
    h := l;
    m := g;
    g := m;
}

atomic action {:layer 1} B() {
    var {:linear} l: Map int int;
    var {:linear "no_collect_keys"} m: Map int int;
    l := g;
    m := h;
}

atomic action {:layer 1} X1({:linear "no_collect_keys"} a: Map int int)
{
    
}

atomic action {:layer 1} Y1()
{
    var {:linear} l: Map int int;
    call l := Map_MakeEmpty();
    call X1(l);
}

atomic action {:layer 1} X2({:linear } a: Map int int)
{
    
}

atomic action {:layer 1} Y2()
{
    var {:linear "no_collect_keys"} l: Map int int;
    call l := Map_MakeEmpty();
    call X2(l);
}

atomic action {:layer 1} X3() returns ({:linear "no_collect_keys"} a: Map int int)
{
    call a := Map_MakeEmpty();
}

atomic action {:layer 1} Y3()
{
    var {:linear} l: Map int int;
    call l := X3();
}

atomic action {:layer 1} X4() returns ({:linear} a: Map int int)
{
    call a := Map_MakeEmpty();
}

datatype D { D({:linear "no_collect_keys"} d: Map int int) }

datatype E { E({:linear} e: Map int int) }

atomic action {:layer 1} Y4()
{
    var {:linear "no_collect_keys"} l: Map int int;
    var {:linear} l': Map int int;
    var {:linear} d: D;
    var {:linear "no_collect_keys"} e: E;

    call l := X4();
    d := D(l);
    D(l) := d;

    call l' := Map_MakeEmpty();
    d := D(l');
    D(l') := d;

    e := E(l');
    e := E(l);
}

atomic action {:layer 1} C() {
    var {:linear "no_collect_keys"} l: Map int int;
    var {:linear} l': Map int int;
    var {:linear} s: Set int;
    var m: [int]int;
    var {:linear} one_int: One int;
    var i: int;

    call l := Map_MakeEmpty();
    call l' := Map_MakeEmpty();

    call s, m := Map_Unpack(l);
    call one_int, i := Map_Get(l, 0);
    call Map_Put(l, one_int, i);
    call i := Map_GetValue(l', 0);
    call Map_PutValue(l', 0, i);
    call l' := Map_Split(l, s);
    call Map_Join(l', l);
    call l := Map_Split(l', s);
    call Map_Join(l, l');
}