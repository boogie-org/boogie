// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure {:yields} {:layer 5} foo()
{
    var {:layer 1} x: int;
    var y: int;

    x, y := y, x;
    yield;
    assume x == y;
}
