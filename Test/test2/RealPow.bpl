// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure Congruent(x: real, y: real, z: real)
{
  assume y == z;
  assert x ** y == x ** z;
}

procedure NotInterpreted()
{
  assert 2e0 ** 2e0 == 4e0;  // real_pow has no axioms
}
