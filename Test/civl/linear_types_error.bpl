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

procedure {:atomic} {:layer 1, 2} A4({:linear_in} path: Lmap Foo, x: Ref Foo, l: Lmap int) returns (path': Lmap Foo)
{
    path' := path;
    call Lmap_Transfer(path'->val[x]->f, l);
}

procedure {:atomic} {:layer 1, 2} A5({:linear_out} path: Lmap int) { }