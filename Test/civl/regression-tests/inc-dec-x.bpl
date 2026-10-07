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

yield procedure {:layer 0} geq0_inc ();
refines right action {:layer 1} GEQ0_INC
{
  assert x >= 0;
  x := x + 1;
}

yield procedure {:layer 0} geq0_dec ();
refines atomic action {:layer 1} GEQ0_DEC
{
  assert x >= 0;
  x := x - 1;
}
