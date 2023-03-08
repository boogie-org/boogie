// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type {:linear "tid"} X = int;
var {:layer 0,1} x:[int]int;

yield invariant {:layer 1} yield_x({:linear "tid"} tid:int);
invariant x[tid] == 0;

procedure {:atomic}{:layer 1} {:pending_async} A ({:linear "tid"} tid:int)
modifies x;
{
  x[tid] := 1;
}

procedure {:left}{:layer 1} {:creates "A"} ASYNC_A ({:linear_in "tid"} tid:int)
{
  call create_async(A(tid));
}

procedure {:yields}{:layer 1} dummy () {}
