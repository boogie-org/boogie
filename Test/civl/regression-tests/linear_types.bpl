// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

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

datatype Foo { Foo(f: Lheap int) }

atomic action {:layer 1, 2} A8({:linear_out} l: Lval int, {:linear_in} path: Lset int) returns (path': Lset int)
{
    path' := path;
    call Lval_Split(path', l);
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
