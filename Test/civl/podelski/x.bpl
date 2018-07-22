// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} x:int;

function {:inline} Inv (x:int) : bool
{
  x >= 0
}

procedure {:yields}{:layer 2} main ()
requires {:layer 1} Inv(x);
{
  yield; assert {:layer 1} Inv(x);
  while (*)
  invariant {:layer 1} Inv(x);
  {
    async call incdec();
    yield; assert {:layer 1} Inv(x);
  }
  yield;
}

procedure {:yields}{:layer 1} incdec()
requires {:layer 1} Inv(x);
ensures  {:layer 1} Inv(x);
{
  yield; assert {:layer 1} Inv(x);
  call geq0_inc();
  call geq0_dec();
  yield; assert {:layer 1} Inv(x);
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
