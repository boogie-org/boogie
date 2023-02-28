// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type {:linear "tid"} Tid = int;
var {:layer 0,1} x:int;

procedure {:yields}{:layer 1} {:yield_requires "Yield_P", tid1, tid2}
P({:linear_in "tid"} tid1:int, {:linear "tid"} tid2:int)
{
  async call Q(tid1);
  call write(); // This action invalidates the precondition of the above async call
}

procedure {:yields}{:layer 1} {:yield_requires "Yield_Q", tid1}
Q({:linear "tid"} tid1:int)
{
  call assertion();
}

procedure {:left}{:layer 1} WRITE()
modifies x;
{
  x := 1;
}

procedure {:atomic}{:layer 1} ASSERTION()
{
  assert x == 0;
}

procedure {:yields}{:layer 0}{:refines "WRITE"} write();
procedure {:yields}{:layer 0}{:refines "ASSERTION"} assertion();

procedure {:yield_invariant}{:layer 1} Yield_P({:linear "tid"} tid1:int, {:linear "tid"} tid2:int);
requires tid1 == 1;
requires tid2 == 1;
requires x == 0;

procedure {:yield_invariant}{:layer 1} Yield_Q({:linear "tid"} tid1:int);
requires tid1 == 1;
requires x == 0; // This precondition is not valid at the end of procedure P
