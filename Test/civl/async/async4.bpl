// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,2} x:int;

type {:pending_async}{:datatype} PA;
function {:constructor} A_Inc() : PA;

procedure {:both}{:layer 2} A_Add (n: int)
modifies x;
{ assert 0 <= n; x := x + n; }

procedure {:IS_invariant}{:layer 1} INV(n: int) returns ({:pending_async "A_Inc"} PAs: [PA]int)
modifies x;
{
  var {:pool "A"} i: int;
  assert 0 <= n;
  assume {:add_to_pool "A", i} {:add_to_pool "A", i+1} 0 <= i && i <= n;
  x := x + i;
  PAs := MapConst(0)[A_Inc() := n - i];
}

procedure {:atomic}{:layer 1}
{:IS "A_Add","INV"}{:elim "A_Inc"}
Async_Add(n: int) returns ({:pending_async "A_Inc"} PAs: [PA]int)
{
  assert {:add_to_pool "A", 0} 0 <= n;
  PAs := MapConst(0)[A_Inc() := n];
}

procedure {:both}{:layer 1,2} A_Inc ()
modifies x;
{ x := x + 1; }
