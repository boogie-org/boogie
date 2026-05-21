// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} x:int;

yield invariant {:layer 1} Inv ();
preserves x >= 0;

yield procedure {:layer 1} main ()
requires call Inv();
{
  while (*)
  invariant {:yields} true;
  invariant call Inv();
  {
    async call incdec();
  }
}

yield procedure {:layer 1} incdec()
preserves call Inv();
{
  call geq0_inc();
  call geq0_dec();
}

right action {:layer 1} GEQ0_INC ()
modifies x;
{
  assert x >= 0;
  x := x + 1;
}

atomic action {:layer 1} GEQ0_DEC ()
modifies x;
{
  assert x >= 0;
  x := x - 1;
}

yield procedure {:layer 0} geq0_inc ();
refines GEQ0_INC;

yield procedure {:layer 0} geq0_dec ();
refines GEQ0_DEC;
