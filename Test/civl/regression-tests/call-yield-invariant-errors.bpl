// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} x:int;
yield invariant {:layer 1} linear_yield_x({:linear} n: int);
preserves x >= n;

yield procedure {:layer 1}
p2({:linear_in} b: int);

yield procedure {:layer 1}
P1({:linear} x: int, {:linear_in} y: int)
{
  call Q(x) | Q(x);
}

yield procedure {:layer 1}
P2({:linear} x: int, {:linear_in} y: int)
{
  call Q(x) | linear_yield_x(y) | linear_yield_x(y);
  call Q(x) | linear_yield_x(x) | linear_yield_x(y);
}

yield procedure {:layer 1}
Q({:linear} a: int);
