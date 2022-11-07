// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure {:atomic} {:layer 1, 2} A0({:linear_in} path: Lmap int, k: [Ref int]bool) returns (path': Lmap int, l: Lmap int) {
    call path' := Lmap_Empty();
    call Lmap_Transfer(path, path');
    call l := Lmap_Split(k, path');
}

procedure {:atomic} {:layer 1, 2} A1({:linear_in} path: Lmap int, k: Ref int, v: int) returns (path': Lmap int, v': int) {
    call path' := Lmap_Empty();
    call Lmap_Transfer(path, path');
    call Lmap_Write(path', k, v);
    call v' := Lmap_Read(path', k);
}

procedure {:atomic} {:layer 1, 2} A2(v: int) returns (path': Lmap int, v': int) {
    var k: Ref int;
    call path' := Lmap_Empty();
    call k := Lmap_Add(path', v);
    call v' := Lmap_Remove(path', k);
}

procedure {:atomic} {:layer 1, 2} A3({:linear_in} path: Lset int, {:linear_out} l: Lset int) returns (path': Lset int) {
    call path' := Lset_Empty();
    call Lset_Transfer(path, path');
    call Lset_Split(l, path');
}

procedure {:atomic} {:layer 1, 2} A4({:linear_in} path: Lset int, l: Lval int) returns (path': Lset int) {
    call path' := Lset_Empty();
    call Lset_Transfer(path, path');
    call Lval_Transfer(l, path');
    call Lval_Split(l, path');
}

procedure {:atomic} {:layer 1, 2} A5({:linear_in} path: Lmap int) returns (path': Lmap int) {
    path' := path;
}

var {:layer 0, 2} g: Lmap int;

procedure {:atomic} {:layer 1, 2} A6({:linear_in} path: Lmap int) returns (path': Lmap int)
modifies g;
{
    path' := path;
    call Lmap_Transfer(g, path');
    call g := Lmap_Empty();
}

type {:datatype} Foo;
function {:constructor} Foo(f: Lmap int): Foo;

procedure {:atomic} {:layer 1, 2} A7({:linear_in} path: Lmap Foo, x: Ref Foo, y: Ref int) returns (path': Lmap Foo)
{
    var l: Lmap int;
    path' := path;
    call l := Lmap_Split(MapOne(y), path'->val[x]->f);
}

procedure {:atomic} {:layer 1, 2} A8({:linear_out} l: Lval int, {:linear_in} path: Lset int) returns (path': Lset int)
{
    path' := path;
    call Lval_Split(l, path');
}

procedure {:atomic} {:layer 1, 2} A9({:linear_in} path1: Lmap int, x: Ref Foo) returns (path2: Lmap Foo)
{
    call path2 := Lmap_Empty();
    call Lmap_Transfer(path1, path2->val[x]->f);
}

procedure {:atomic} {:layer 1, 2} A10({:linear_in} a: Foo) returns (b: Foo)
{
    var x: Lmap int;
    Foo(x) := a;
    b := Foo(x);
}
