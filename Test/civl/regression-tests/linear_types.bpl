// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

atomic action {:layer 1, 2} A3({:linear_in} path: Lset int, {:linear_out} l: Lset int) returns (path': Lset int) {
    call path' := Lset_Empty();
    call Lset_Put(path', path);
    call Lset_Split(path', l);
}

atomic action {:layer 1, 2} A5({:linear_in} path: Lheap int) returns (path': Lheap int) {
    path' := path;
}

var {:layer 0, 2} g: Lheap int;

datatype Foo { Foo(f: Lheap int) }

atomic action {:layer 1, 2} A10({:linear_in} a: Foo) returns (b: Foo)
{
    var x: Lheap int;
    Foo(x) := a;
    b := Foo(x);
}
