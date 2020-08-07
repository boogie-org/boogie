// RUN: %boogie -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} x:int;

procedure {:yield_invariant} {:layer 1} yield_x(n: int);
requires x >= n;

type {:pending_async}{:datatype} PA;
function {:pending_async "A"}{:constructor} A_PA() : PA;

function {:inline} NoPAs () : [PA]int
{ (lambda pa:PA :: 0) }

procedure {:atomic}{:layer 1} A ()
modifies x;
{
  x := x + 1;
}

procedure {:left}{:layer 1} ASYNC_A () returns ({:pending_async "A"} PAs:[PA]int)
{
  PAs := NoPAs()[A_PA() := 1];
}

procedure {:yields}{:layer 1} dummy () {}
