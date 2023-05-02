// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,2} x:int;

////////////////////////////////////////////////////////////////////////////////

>-< action {:layer 1} MAIN ()
refines MAIN' using INV;
creates INC, DEC;
{
  call create_async(INC());
  call create_async(DEC());
}

>-< action {:layer 2} MAIN' ()
{
}

invariant action {:layer 1}
INV ()
creates INC, DEC;
modifies x;
{
  if (*) { call create_async(INC()); } else { x := x + 1; }
  if (*) { call create_async(DEC()); } else { x := x - 1; }
}

////////////////////////////////////////////////////////////////////////////////

async <- action {:layer 1} INC ()
modifies x;
{
  x := x + 1;
}

async <- action {:layer 1} DEC ()
modifies x;
{
  x := x - 1;
}
