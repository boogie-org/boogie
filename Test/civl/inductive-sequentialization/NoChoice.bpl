// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,2} x:int;

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 1}
{:creates "INC", "DEC"}
{:IS "MAIN'","INV"}
MAIN ()
{
  call create_async(INC());
  call create_async(DEC());
}

procedure {:atomic}{:layer 2}
MAIN' ()
{
}

procedure {:layer 1}
{:creates "INC", "DEC"}
{:IS_invariant}{:elim "INC"}{:elim "DEC"}
INV ()
modifies x;
{
  if (*) { call create_async(INC()); } else { x := x + 1; }
  if (*) { call create_async(DEC()); } else { x := x - 1; }
}

////////////////////////////////////////////////////////////////////////////////

procedure {:left}{:layer 1}
{:pending_async}
INC ()
modifies x;
{
  x := x + 1;
}

procedure {:left}{:layer 1}
{:pending_async}
DEC ()
modifies x;
{
  x := x - 1;
}
