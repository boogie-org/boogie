// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure {:atomic} {:layer 1, 2} A0(path: Lmap int, k: [Ref int]bool) returns (path': Lmap int, l: Lmap int) {
    call path' := Lmap_Empty();
    call Lmap_Transfer(path, path');
    call l := Lmap_Split(path', k);
}

procedure {:atomic} {:layer 1, 2} A1(path: Lmap int, k: Ref int, v: int) returns (path': Lmap int, v': int) {
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

procedure {:atomic} {:layer 1, 2} A3(path: Lset int, k: [int]bool) returns (path': Lset int, l: Lset int) {
    call path' := Lset_Empty();
    call Lset_Transfer(path, path');
    call l := Lset_Split(path', k);
}

procedure {:atomic} {:layer 1, 2} A4(path: Lset int, k: int) returns (path': Lset int) {
    var l: Lval int;
    call path' := Lset_Empty();
    call Lset_Transfer(path, path');
    call l := Lval_Split(path', k);
    call Lval_Transfer(l, path');
}
