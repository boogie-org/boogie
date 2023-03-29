// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,2} x:int;

<-> action {:layer 2} A_Add (n: int)
modifies x;
{ assert 0 <= n; x := x + n; }

invariant action {:layer 1} INV(n: int)
creates A_Inc;
modifies x;
{
  var {:pool "A"} i: int;
  assert 0 <= n;
  assume {:add_to_pool "A", i} {:add_to_pool "A", i+1} 0 <= i && i <= n;
  x := x + i;
  call create_multi_asyncs(MapConst(0)[A_Inc() := n - i]);
}

action {:layer 1} Async_Add(n: int) refines A_Add using INV
creates A_Inc;
{
  assert 0 <= n;
  assume {:add_to_pool "A", 0} true;
  call create_multi_asyncs(MapConst(0)[A_Inc() := n]);
}

async <-> action {:layer 1,2} A_Inc ()
modifies x;
{ x := x + 1; }
