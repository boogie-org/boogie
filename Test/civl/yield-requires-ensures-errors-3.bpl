// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "lin"} X = int;

var {:layer 0,1} x:int;

yield invariant {:layer 1} linear_yield_x({:linear "lin"} n: int);
invariant x >= n;

yield procedure {:layer 1} p1(a: int) returns (c: int)
requires call linear_yield_x(a);
{
}
