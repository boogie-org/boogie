// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type {:linear "tid"} Tid = int;
var {:layer 0,1} x:int;

procedure {:yields}{:layer 1} P({:linear_in "tid"} tid1:int, {:linear "tid"} tid2:int)
requires {:layer 1} tid1 == 1;
requires {:layer 1} tid2 == 2;
requires {:layer 1} x == 0;
{
  async call Q(tid1);
  call write(); // This action invalidates the precondition of the above async call
}

procedure {:yields}{:layer 1} Q({:linear "tid"} tid1:int)
requires {:layer 1} tid1 == 1;
requires {:layer 1} x == 0; // This precondition is not valid at the end of procedure P
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
