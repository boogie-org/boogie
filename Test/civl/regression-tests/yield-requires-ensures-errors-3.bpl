// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} x:int;

yield invariant {:layer 1} linear_yield_x({:linear} n: One int);
preserves x >= n->val;

yield procedure {:layer 1} p1(a: One int) returns (c: int)
requires call linear_yield_x(a);
{
}
