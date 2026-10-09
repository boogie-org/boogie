// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// real_pow is declared for the axiom, so the procedure's query must not declare it again.
axiom (forall x: real :: x ** 1e0 == x);

procedure P(x: real)
{
  assert x ** 1e0 == x;
}
