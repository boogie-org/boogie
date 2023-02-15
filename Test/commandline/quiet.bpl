// RUN: %parallel-boogie -quiet "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure BadAssert()
{
  assert 1 == 2;
}
