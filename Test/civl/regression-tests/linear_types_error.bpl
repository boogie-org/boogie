// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

atomic action {:layer 1, 2} A0(path: Lheap int) returns (l: Lheap int) { }

atomic action {:layer 1, 2} A1(path: Lheap int) returns (path': Lheap int) {
    path' := path;
}

atomic action {:layer 1, 2} A2(path: Lheap int) returns (path': Lheap int) { var k: Lset (Ref int);
    call path' := Lmap_Empty();
    call k := Lmap_Free(path);
}

var {:layer 0, 2} g: Lheap int;

datatype Foo { Foo(f: Lheap int) }

atomic action {:layer 1, 2} A5({:linear_out} path: Lheap int) { }

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

yield procedure {:layer 1} Foo1(x: Lheap int)
{
  call Lmap_Assume(x, x);
}

yield procedure {:layer 1} Foo2(x: Foo)
{
  call Lmap_Assume(x->f, x->f);
}

