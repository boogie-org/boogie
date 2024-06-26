// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

yield procedure {:layer 5} foo()
{
    var {:layer 1} x: int;
    var y: int;

    x, y := y, x;
    assume x == y;
}
