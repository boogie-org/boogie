// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,2} x:int;

procedure {:yields}{:layer 1}{:refines "A_Inc"} Service ()
{
  async call {:sync} Callback();
}

procedure {:both}{:layer 1,2} A_Inc ()
modifies x;
{ x := x + 1; }
procedure {:yields}{:layer 0}{:refines "A_Inc"} Callback ();
