// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

atomic action {:layer 1, 2} A0(path: Lheap int) returns (l: Lheap int) { }

atomic action {:layer 1, 2} A1(path: Lheap int) returns (path': Lheap int) {
    path' := path;
}

atomic action {:layer 1, 2} A2(path: Lheap int) returns (path': Lheap int) {
    call path' := Lheap_Empty();
    call Lheap_Transfer(path, path');
}

var {:layer 0, 2} g: Lheap int;

atomic action {:layer 1, 2} A3({:linear_in} path: Lheap int) returns (path': Lheap int)
{
    path' := path;
    call Lheap_Transfer(g, path');
}

datatype Foo { Foo(f: Lheap int) }


atomic action {:layer 1, 2} A4({:linear_in} path: Lheap Foo, x: Ref Foo, {:linear_in} l: Lheap int) returns (path': Lheap Foo, l': Lheap int)
{
    path' := path;
    l' := l;
    call Lheap_Transfer(path'->val[x]->f, l');
}

atomic action {:layer 1, 2} A5({:linear_out} path: Lheap int) { }

atomic action {:layer 1, 2} A6({:linear_in} path: Lheap int) returns (path': Lheap int)
{
    path' := path;
    call Lheap_Transfer(path', path');
}

atomic action {:layer 1, 2} A7(path1: Lheap int, {:linear_in} path2: Lheap int) returns (path': Lheap int)
{
    path' := path2;
    call Lheap_Transfer(path1, path');
}

atomic action {:layer 1, 2} A8({:linear_in} path1: Lheap int, x: Ref Foo) returns (path2: Lheap Foo)
{
    call Lheap_Transfer(path1, path2->val[x]->f);
}

atomic action {:layer 1, 2} A9({:linear_in} l: Lheap int)
{
    call Lheap_Transfer(l, g);
}

atomic action {:layer 1, 2} A10({:linear_in} l: Lheap int, l': Lheap int)
{
    call Lheap_Transfer(l, l');
}

atomic action {:layer 1, 2} A11({:linear_in} a: Foo) returns (b: Foo)
{
    var x: Lheap int;
    Foo(x) := a;
}

atomic action {:layer 1, 2} A12({:linear_in} a: Foo) returns (b: Foo)
{
    var x: Lheap int;
    b := a;
    Foo(x) := a;
}

atomic action {:layer 1, 2} A13({:linear_in} a: Foo) returns (b: Foo)
{
    var x: Lheap int;
    b := Foo(x);
}

datatype Bar { Bar(x: Lval int, y: int) }

atomic action {:layer 1, 2} A14({:linear_in} a: Lval int) returns (b: Bar)
{
    b := Bar(Lval(3), 3+4);
}

type {:linear "X"} X = int;
yield procedure {:layer 1} A15({:linear_in "X"} a: Lval int);
