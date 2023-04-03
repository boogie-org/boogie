// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var{:layer 20,40} x:int;

<-> action {:layer 21,25} atomic_p_gt1_lower()
modifies x;
{ x := x + 1; }

yield procedure {:layer 20} p_gt1_lower();
refines atomic_p_gt1_lower;

<-> action {:layer 26,40} atomic_p_gt1()
modifies x;
{ x := x + 1; }

yield procedure {:layer 25} p_gt1()
refines atomic_p_gt1;
{
  call p_gt1_lower();
}

<-> action {:layer 21,40} atomic_p_gt2()
{ assert x == 0; }

yield procedure {:layer 20} p_gt2();
refines atomic_p_gt2;
