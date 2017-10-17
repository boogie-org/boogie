// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure{:yields}{:layer 94} Test()
{
  yield;
  L:
  yield;
}

procedure{:yields}{:layer 94} Test2()
{
  yield;
  assert{:layer 94} 2 + 2 == 3;
  L:
  yield;
}
