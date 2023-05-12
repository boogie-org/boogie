// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type {:linear "tid"} Tid = int;
var {:layer 0,1} x:int;

yield procedure {:layer 1} P({:linear_in "tid"} tid1:int, {:linear "tid"} tid2:int)
requires call Yield_P(tid1, tid2);
{
  async call Q(tid1);
  call write(); // This action invalidates the precondition of the above async call
}

yield procedure {:layer 1} Q({:linear "tid"} tid1:int)
requires call Yield_Q(tid1);
{
  call assertion();
}

left action {:layer 1} WRITE()
modifies x;
{
  x := 1;
}

atomic action {:layer 1} ASSERTION()
{
  assert x == 0;
}

yield procedure {:layer 0} write();
refines WRITE;

yield procedure {:layer 0} assertion();
refines ASSERTION;

yield invariant {:layer 1} Yield_P({:linear "tid"} tid1:int, {:linear "tid"} tid2:int);
invariant tid1 == 1;
invariant tid2 == 1;
invariant x == 0;

yield invariant {:layer 1} Yield_Q({:linear "tid"} tid1:int);
invariant tid1 == 1;
invariant x == 0; // This precondition is not valid at the end of procedure P
