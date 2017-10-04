// RUN: %boogie -noinfer -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var{:layer 1,1} x:int;

procedure{:layer 1} P1(i:int);
procedure P2(j:int);

procedure{:yields}{:layer 1} A1({:layer 1}i:int)
{
  yield;
  call P1(i);
  call P2(i);
  yield;
}
