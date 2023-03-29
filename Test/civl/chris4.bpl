// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure{:yields}{:layer 94} Test()
{
  assert{:layer 94} 2 + 2 == 3;
}
