// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} s:int;
var {:layer 0,1} t:int;

yield invariant {:layer 1} Inv ();
invariant t == s;

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

-> action {:layer 1} INC_T ()
modifies t;
{
  assert s <= t;
  t := t + 1;
}

action {:layer 1} INC_S ()
modifies s;
{
  assert s < t;
  s := s + 1;
}

yield procedure {:layer 0} inc_t ();
refines INC_T;

yield procedure {:layer 0} inc_s ();
refines INC_S;
