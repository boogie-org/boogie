// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,3} x:int;

yield procedure {:layer 2} Client ()
refines A_Inc;
{
  call Service();
}

>-< action {:layer 1} A_Service()
refines A_Inc;
creates A_Inc;
{
  call create_async(A_Inc());
}
yield procedure {:layer 0} Service ()
refines A_Service;
{
  async call Callback();
}

async <-> action {:layer 1,3} A_Inc ()
modifies x;
{ x := x + 1; }
yield procedure {:layer 0} Callback ();
refines A_Inc;
