// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type {:linear "tid"} X = int;
var {:layer 0,1} x:[int]int;

procedure {:yield_invariant} {:layer 1} yield_x({:linear "tid"} tid:int);
requires x[tid] == 0;

type {:pending_async}{:datatype} PA;
function {:constructor} A(tid:int) : PA;

function {:inline} NoPAs () : [PA]int
{ (lambda pa:PA :: 0) }

procedure {:atomic}{:layer 1} A ({:linear "tid"} tid:int)
modifies x;
{
  x[tid] := 1;
}

procedure {:left}{:layer 1} ASYNC_A ({:linear_in "tid"} tid:int) returns ({:pending_async "A"} PAs:[PA]int)
{
  PAs := NoPAs()[A(tid) := 1];
}

procedure {:yields}{:layer 1} dummy () {}
