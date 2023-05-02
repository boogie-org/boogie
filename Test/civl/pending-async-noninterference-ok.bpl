// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} x:int;

yield invariant {:layer 1} yield_x(n: int);
invariant x >= n;

async >-< action {:layer 1} A ()
modifies x;
{
  x := x + 1;
}

<- action {:layer 1} ASYNC_A ()
creates A;
{
  call create_async(A());
}

yield procedure {:layer 1} dummy () {}
