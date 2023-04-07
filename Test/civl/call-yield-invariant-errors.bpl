// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "lin"} X = int;
var {:layer 0,1} x:int;
yield invariant {:layer 1} linear_yield_x({:linear "lin"} n: int);
invariant x >= n;

yield procedure {:layer 1}
p2({:linear_in "lin"} b: int);

yield procedure {:layer 1}
P1({:linear "lin"} x: int, {:linear_in "lin"} y: int)
{
  par Q(x) | Q(x);
}

yield procedure {:layer 1}
P2({:linear "lin"} x: int, {:linear_in "lin"} y: int)
{
  par Q(x) | linear_yield_x(y) | linear_yield_x(y);
  par Q(x) | linear_yield_x(x) | linear_yield_x(y);
}

yield procedure {:layer 1}
Q({:linear "lin"} a: int);
