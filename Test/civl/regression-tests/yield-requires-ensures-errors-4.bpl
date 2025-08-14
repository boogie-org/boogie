// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "lin"} X = int;

var {:layer 0,1} x:int;

yield invariant {:layer 1} linear_yield_x({:linear "lin"} n: int);
preserves x >= n;

yield procedure {:layer 1}
p3({:linear "lin"} a: int, {:linear_in "lin"} b: int, {:linear_out "lin"} c: int);
requires call linear_yield_x(a);
ensures call linear_yield_x(a);
requires call linear_yield_x(c);
ensures call linear_yield_x(b);
preserves call linear_yield_x(c);
