// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} s:int;
var {:layer 0,1} t:int;

function {:inline} Inv (s:int, t:int) : bool
{
  t == s
// t >= s
}

procedure {:yields}{:layer 2} main ()
requires {:layer 1} s == t;
{
  yield; assert {:layer 1} Inv(s, t);
  while (*)
  invariant {:layer 1} Inv(s, t);
  {
    async call incdec();
    yield; assert {:layer 1} Inv(s, t);
  }
  yield;
}

procedure {:yields}{:layer 1} incdec()
requires {:layer 1} Inv(s, t);
ensures  {:layer 1} Inv(s, t);
{
  yield; assert {:layer 1} Inv(s, t);
  call inc_t();
  call inc_s();
  yield; assert {:layer 1} Inv(s, t);
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
