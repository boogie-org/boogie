// RUN: %parallel-boogie /monomorphize "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure p(x: int) {
    var m: <A>[A]bool;
    m[true] := false;
    m[x] := false;
    assert m[x] == false;
}
