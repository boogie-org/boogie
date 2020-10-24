// RUN: %boogie "%s" > "%t"
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
  invariant {:yields} {:layer 1} {:yield_loop "linear_yield_x", a} true;
  invariant {:yields} {:layer 1} {:yield_loop "linear_yield_x", b} true;
  invariant {:yields} {:layer 1} {:yield_loop "linear_yield_x", c} true;
  {}
}

procedure {:yields} {:layer 1}
p2({:linear_in "lin"} b: int);

function {:builtin "MapConst"} MapConstBool(bool) : [int]bool;
function {:inline} {:linear "lin"} TidCollector(x: int) : [int]bool
{
  MapConstBool(false)[x := true]
}
