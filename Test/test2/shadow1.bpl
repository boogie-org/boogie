// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var x:int;

procedure P()
requires x == 0;
{
  assert (forall y:int :: x == 0); // x should be global variable
  assert (forall x:int :: x == 0); // x should be bound variable
}
