// RUN: %boogie -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 1,1} g:int;

procedure {:intro} {:layer 1} P(x:int)
{
  assert x == 0;
}

procedure{:yields}{:layer 1} Y(x:int)
{
  call P(x);
  assert{:layer 1} x == 0;
}
