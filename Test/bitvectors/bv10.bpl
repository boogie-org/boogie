// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var x: bv32;

procedure main() 
modifies x;
{

  x := 0bv32;
  assume x == 1bv32;
  assert false;
}
