// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "lin"} X = int;

var {:layer 0,1} x:int;

yield invariant {:layer 1} yield_x(n: int);
invariant x >= n;

yield procedure {:layer 1} p2({:layer 0,0} a: int) returns (c: int)
requires call yield_x(a);
ensures call yield_x(a + c);
{
}
