// RUN: %parallel-boogie "%s" > "%t"
procedure P(x: int, y: int) {
    var z: int;
    var w: int;

    z := (var a, b := x+1, y+1; a);
    w := (var a, b := x+1, y+1; b);
    assert (z - 1) == x;
    assert (w - 1) == y;
}
