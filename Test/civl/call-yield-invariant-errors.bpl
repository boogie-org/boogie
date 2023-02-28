// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "lin"} X = int;
var {:layer 0,1} x:int;
procedure {:yield_invariant} {:layer 1} linear_yield_x({:linear "lin"} n: int);
requires x >= n;

procedure {:yields} {:layer 1}
p1({:linear "lin"} a: int, {:linear_in "lin"} b: int, c: int)
{
  call p2(b);
  while (*)
  invariant {:yields}
  {:yield_loop "linear_yield_x", a}
  {:yield_loop "linear_yield_x", b}
  {:yield_loop "linear_yield_x", c} true;
  {}
}

procedure {:yields} {:layer 1}
p2({:linear_in "lin"} b: int);

procedure {:yields} {:layer 1}
P1({:linear "lin"} x: int, {:linear_in "lin"} y: int)
{
  par Q(x) | Q(x);
}

procedure {:yields} {:layer 1}
P2({:linear "lin"} x: int, {:linear_in "lin"} y: int)
{
  par Q(x) | linear_yield_x(y) | linear_yield_x(y);
  par Q(x) | linear_yield_x(x) | linear_yield_x(y);
}

procedure {:yields} {:layer 1}
Q({:linear "lin"} a: int);
