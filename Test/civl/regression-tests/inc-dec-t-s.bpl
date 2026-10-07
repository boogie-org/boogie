// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} s:int;
var {:layer 0,1} t:int;

yield invariant {:layer 1} Inv ();
preserves t == s;

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
  call inc_t();
  call inc_s();
}

yield procedure {:layer 0} inc_t ();
refines right action {:layer 1} INC_T
{
  assert s <= t;
  t := t + 1;
}

yield procedure {:layer 0} inc_s ();
refines atomic action {:layer 1} INC_S
{
  assert s < t;
  s := s + 1;
}
