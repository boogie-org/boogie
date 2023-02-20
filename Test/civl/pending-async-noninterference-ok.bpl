// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} x:int;

procedure {:yield_invariant} {:layer 1} yield_x(n: int);
requires x >= n;

procedure {:atomic}{:layer 1} {:pending_async} A ()
modifies x;
{
  x := x + 1;
}

procedure {:left}{:layer 1} {:creates "A"} ASYNC_A ()
{
  call create_async(A());
}

procedure {:yields}{:layer 1} dummy () {}
