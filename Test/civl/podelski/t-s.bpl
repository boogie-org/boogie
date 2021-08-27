// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} s:int;
var {:layer 0,1} t:int;

procedure {:yield_invariant}{:layer 1} Inv ();
requires t == s;
// requires t >= s;

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
  call inc_t();
  call inc_s();
}

procedure {:right}{:layer 1} INC_T ()
modifies t;
{
  assert s <= t;
  t := t + 1;
}

procedure {:atomic}{:layer 1} INC_S ()
modifies s;
{
  assert s < t;
  s := s + 1;
}

procedure {:yields}{:layer 0}{:refines "INC_T"} inc_t ();
procedure {:yields}{:layer 0}{:refines "INC_S"} inc_s ();
