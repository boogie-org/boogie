// RUN: %parallel-boogie -silent "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure BadAssert()
{
  assert 1 == 2;
}
