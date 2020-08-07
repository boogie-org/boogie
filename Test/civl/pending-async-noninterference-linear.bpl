// RUN: %boogie -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} x:[int]int;

procedure {:yield_invariant} {:layer 1} yield_x({:linear "tid"} tid:int);
requires x[tid] == 0;

type {:pending_async}{:datatype} PA;
function {:pending_async "A"}{:constructor} A_PA(tid:int) : PA;

function {:inline} NoPAs () : [PA]int
{ (lambda pa:PA :: 0) }

procedure {:atomic}{:layer 1} A ({:linear "tid"} tid:int)
modifies x;
{
  x[tid] := 1;
}

procedure {:left}{:layer 1} ASYNC_A ({:linear_in "tid"} tid:int) returns ({:pending_async "A"} PAs:[PA]int)
{
  PAs := NoPAs()[A_PA(tid) := 1];
}

procedure {:yields}{:layer 1} dummy () {}

function {:builtin "MapConst"} MapConstBool(bool): [int]bool;
function {:builtin "MapOr"} MapOr([int]bool, [int]bool) : [int]bool;

function {:inline} {:linear "tid"} TidCollector(x: int) : [int]bool
{
  MapConstBool(false)[x := true]
}
function {:inline} {:linear "tid"} TidSetCollector(x: [int]bool) : [int]bool
{
  x
}
