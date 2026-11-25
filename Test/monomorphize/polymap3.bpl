// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:inline} setFalse(m: <A>[A]bool, x: int): <A>[A]bool {
    m[x := false]
}

procedure p(x: int) {
    var m: <A>[A]bool;
    m[true] := false;
    m := setFalse(m, x);
    assert m[x] == false;
    assert m[true] == false;
}
