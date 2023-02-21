// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,3} x:int;

procedure {:yields}{:layer 2}{:refines "A_Inc"} Client ()
{
  call Service();
}

procedure {:layer 1}
{:creates "A_Inc"}
{:IS_invariant}{:elim "A_Inc"}
INV()
modifies x;
{
  if (*) {
    call create_async(A_Inc());
  } else {
    x := x + 1;
  }
}

procedure {:atomic}{:layer 1}
{:creates "A_Inc"}
{:IS "A_Inc","INV"}
A_Service()
{
  call create_async(A_Inc());
}
procedure {:yields}{:layer 0}{:refines "A_Service"} Service ()
{
  async call Callback();
}

procedure {:both}{:layer 1,3}
{:pending_async}
A_Inc ()
modifies x;
{ x := x + 1; }
procedure {:yields}{:layer 0}{:refines "A_Inc"} Callback ();
