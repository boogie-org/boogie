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
