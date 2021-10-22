// RUN: %parallel-boogie /errorLimit:2 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure ManyErrors(x0: int, x1: int, x2: int)
  ensures x0 == 1;
  ensures x1 == 2;
  ensures x2 == 3;
{
}