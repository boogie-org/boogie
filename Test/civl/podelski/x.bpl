// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} x:int;

procedure {:yield_invariant}{:layer 1} Inv ();
requires x >= 0;

procedure {:yields}{:layer 1}
{:yield_requires "Inv"}
main ()
{
  while (*)
  invariant {:yields}{:layer 1}{:yield_loop "Inv"} true;
  {
    async call incdec();
  }
}

procedure {:yields}{:layer 1}
{:yield_preserves "Inv"}
incdec()
{
  call geq0_inc();
  call geq0_dec();
}

procedure {:right}{:layer 1} GEQ0_INC ()
modifies x;
{
  assert x >= 0;
  x := x + 1;
}

procedure {:atomic}{:layer 1} GEQ0_DEC ()
modifies x;
{
  assert x >= 0;
  x := x - 1;
}

procedure {:yields}{:layer 0}{:refines "GEQ0_INC"} geq0_inc ();
procedure {:yields}{:layer 0}{:refines "GEQ0_DEC"} geq0_dec ();
