// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure {:atomic} {:layer 1, 2} A0(path: Lmap int) returns (l: Lmap int) { }

procedure {:atomic} {:layer 1, 2} A1(path: Lmap int) returns (path': Lmap int) {
    path' := path;
}

procedure {:atomic} {:layer 1, 2} A2(path: Lmap int) returns (path': Lmap int) {
    call path' := Lmap_Empty();
    call Lmap_Transfer(path, path');
}

var {:layer 0, 2} g: Lmap int;

procedure {:atomic} {:layer 1, 2} A3({:linear_in} path: Lmap int) returns (path': Lmap int)
{
    path' := path;
    call Lmap_Transfer(g, path');
}

type {:datatype} Foo;
function {:constructor} Foo(f: Lmap int): Foo;

procedure {:atomic} {:layer 1, 2} A4({:linear_in} path: Lmap Foo, x: Ref Foo, {:linear_in} l: Lmap int) returns (path': Lmap Foo, l': Lmap int)
{
    path' := path;
    l' := l;
    call Lmap_Transfer(path'->val[x]->f, l');
}

procedure {:atomic} {:layer 1, 2} A5({:linear_out} path: Lmap int) { }

procedure {:atomic} {:layer 1, 2} A6({:linear_in} path: Lmap int) returns (path': Lmap int)
{
    path' := path;
    call Lmap_Transfer(path', path');
}

procedure {:atomic} {:layer 1, 2} A7(path1: Lmap int, {:linear_in} path2: Lmap int) returns (path': Lmap int)
{
    path' := path2;
    call Lmap_Transfer(path1, path');
}

procedure {:atomic} {:layer 1, 2} A8({:linear_in} path1: Lmap int, x: Ref Foo) returns (path2: Lmap Foo)
{
    call Lmap_Transfer(path1, path2->val[x]->f);
}

procedure {:atomic} {:layer 1, 2} A9({:linear_in} l: Lmap int)
{
    call Lmap_Transfer(l, g);
}

procedure {:atomic} {:layer 1, 2} A10({:linear_in} l: Lmap int, l': Lmap int)
{
    call Lmap_Transfer(l, l');
}

procedure {:atomic} {:layer 1, 2} A11({:linear_in} a: Foo) returns (b: Foo)
{
    var x: Lmap int;
    Foo(x) := a;
}

procedure {:atomic} {:layer 1, 2} A12({:linear_in} a: Foo) returns (b: Foo)
{
    var x: Lmap int;
    b := a;
    Foo(x) := a;
}

procedure {:atomic} {:layer 1, 2} A13({:linear_in} a: Foo) returns (b: Foo)
{
    var x: Lmap int;
    b := Foo(x);
}
