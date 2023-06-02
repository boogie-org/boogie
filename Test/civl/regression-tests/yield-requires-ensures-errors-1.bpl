// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} x:int;

yield invariant {:layer 1} yield_x(n: int);
invariant x >= n;

yield procedure {:layer 1} p1(a: int) returns (c: int)
requires call yield_x(c);
preserves call yield_x(c);
ensures call yield_x(c);
ensures call yield_x(a + c);
{
}
