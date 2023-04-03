// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,2} x:int;

yield procedure {:layer 1} Service ()
refines A_Inc;
{
  async call {:sync} Callback();
}

<-> action {:layer 1,2} A_Inc ()
modifies x;
{ x := x + 1; }
yield procedure {:layer 0} Callback ();
refines A_Inc;
