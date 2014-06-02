// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// XFAIL: *
var {:phase 1} x: int;
var {:phase 1} y: int;

procedure {:yields} {:phase 1} foo()
{
  assume x == y;
  x := x + 1;
  async call P();
  y := y + 1;
}

procedure {:yields} {:phase 1} P()
requires x != y;
{
  assert {:phase 1} x != y;
}
