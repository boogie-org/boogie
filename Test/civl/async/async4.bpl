// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,2} x:int;

procedure {:both}{:layer 2} A_Add (n: int)
modifies x;
{ assert 0 <= n; x := x + n; }

procedure {:layer 1}
{:creates "A_Inc"}
{:IS_invariant}{:elim "A_Inc"}
INV(n: int)
modifies x;
{
  var {:pool "A"} i: int;
  assert 0 <= n;
  assume {:add_to_pool "A", i} {:add_to_pool "A", i+1} 0 <= i && i <= n;
  x := x + i;
  call create_multi_asyncs(MapConst(0)[A_Inc() := n - i]);
}

procedure {:atomic}{:layer 1}
{:creates "A_Inc"}
{:IS "A_Add","INV"}
Async_Add(n: int)
{
  assert 0 <= n;
  assume {:add_to_pool "A", 0} true;
  call create_multi_asyncs(MapConst(0)[A_Inc() := n]);
}

procedure {:both}{:layer 1,2}
{:pending_async}
A_Inc ()
modifies x;
{ x := x + 1; }
