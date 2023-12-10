// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

atomic action {:layer 1, 2} A1({:linear_in} path: Lheap int, k: [Ref int]bool) returns (path': Lheap int, l: Lheap int) {
    call path' := Lheap_Empty();
    call Lheap_Put(path', path);
    call l := Lheap_Get(path', k);
}

atomic action {:layer 1, 2} A2(v: int) returns (path': Lheap int) {
    var k: Lval (Ref int);
    call path' := Lheap_Empty();
    call k := Lheap_Alloc(path', v);
    call Lheap_Free(path', k->val);
}

atomic action {:layer 1, 2} A3({:linear_in} path: Lset int, {:linear_out} l: Lset int) returns (path': Lset int) {
    call path' := Lset_Empty();
    call Lset_Put(path', path);
    call Lset_Split(path', l);
}

atomic action {:layer 1, 2} A4({:linear_in} path: Lset int, l: Lval int) returns (path': Lset int) {
    call path' := Lset_Empty();
    call Lset_Put(path', path);
    call Lval_Put(path', l);
    call Lval_Split(path', l);
}

atomic action {:layer 1, 2} A5({:linear_in} path: Lheap int) returns (path': Lheap int) {
    path' := path;
}

var {:layer 0, 2} g: Lheap int;

atomic action {:layer 1, 2} A6({:linear_in} path: Lheap int) returns (path': Lheap int)
modifies g;
{
    path' := path;
    call Lheap_Put(path', g);
    call g := Lheap_Empty();
}

datatype Foo { Foo(f: Lheap int) }

atomic action {:layer 1, 2} A7({:linear_in} path: Lheap Foo, x: Ref Foo, y: Ref int) returns (path': Lheap Foo)
{
    var l: Lheap int;
    path' := path;
    call l := Lheap_Get(path'->val[x]->f, MapOne(y));
}

atomic action {:layer 1, 2} A8({:linear_out} l: Lval int, {:linear_in} path: Lset int) returns (path': Lset int)
{
    path' := path;
    call Lval_Split(path', l);
}

atomic action {:layer 1, 2} A9({:linear_in} path1: Lheap int, x: Ref Foo) returns (path2: Lheap Foo)
{
    call path2 := Lheap_Empty();
    call Lheap_Put(path2->val[x]->f, path1);
}

atomic action {:layer 1, 2} A10({:linear_in} a: Foo) returns (b: Foo)
{
    var x: Lheap int;
    Foo(x) := a;
    b := Foo(x);
}

datatype Bar { Bar(x: Lval int, y: int) }

atomic action {:layer 1, 2} A11({:linear_in} a: Lval int) returns (b: Bar)
{
    b := Bar(a, 3+4);
}
