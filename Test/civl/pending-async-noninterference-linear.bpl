// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type {:linear "tid"} X = int;
var {:layer 0,1} x:[int]int;

yield invariant {:layer 1} yield_x({:linear "tid"} tid:int);
invariant x[tid] == 0;

async action {:layer 1} A ({:linear "tid"} tid:int)
modifies x;
{
  x[tid] := 1;
}

<- action {:layer 1} ASYNC_A ({:linear_in "tid"} tid:int)
 creates A;
{
  call create_async(A(tid));
}

yield procedure {:layer 1} dummy () {}
