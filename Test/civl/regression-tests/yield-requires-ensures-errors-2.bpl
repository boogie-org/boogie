// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} x:int;

yield invariant {:layer 1} yield_x(n: int);
invariant x >= n;

yield procedure {:layer 1} p0(n: int)
requires call yield_x(n == 4);
ensures call yield_x(n == 8);
preserves call yield_x(n == 2);
{
}
