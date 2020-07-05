// RUN: %boogie -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,1} x:int;

procedure {:yield_invariant} {:layer 1} yield_x(n: int);
requires x >= n;

procedure {:yield_invariant} {:layer 1} linear_yield_x({:linear "lin"} n: int);
requires x >= n;

procedure {:yields} {:layer 1}
{:yield_requires "yield_x", x == 4}
{:yield_ensures "yield_x", x == 8}
p0()
{
}

procedure {:yields} {:layer 1}
{:yield_requires "yield_x", c}
{:yield_requires "linear_yield_x", a}
{:yield_ensures "yield_x", a + c}
p1(a: int) returns (c: int)
{
}

procedure {:yields} {:layer 1}
{:yield_requires "yield_x", a}
{:yield_ensures "yield_x", a + c}
p2({:layer 0,0} a: int) returns (c: int)
{
}

procedure {:yields} {:layer 1}
{:yield_requires "linear_yield_x", a}
{:yield_ensures "linear_yield_x", a}
{:yield_requires "linear_yield_x", c}
{:yield_ensures "linear_yield_x", b}
p3({:linear "lin"} a: int, {:linear_in "lin"} b: int, {:linear_out "lin"} c: int);

function {:builtin "MapConst"} MapConstBool(bool) : [int]bool;
function {:inline} {:linear "lin"} TidCollector(x: int) : [int]bool
{
  MapConstBool(false)[x := true]
}
