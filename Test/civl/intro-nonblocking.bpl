// RUN: %boogie -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure {:intro}{:layer 1} intro (x:int)
{
  assume x == 0;
}

procedure {:yields}{:layer 1} p (x:int)
{
  yield;
  call intro(x);
  yield;
}
