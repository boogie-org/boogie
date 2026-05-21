// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} x:int;

yield invariant {:layer 1} yield_x(n: int);
preserves x >= n;

yield atomic procedure {:layer 1} p2(a: int) returns (c: int)
requires call yield_x(a);
preserves call yield_x(a);
ensures call yield_x(a + c);
{
}
