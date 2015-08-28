// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure{:yields}{:layer 94,94} H()
{
  yield;
}

procedure{:yields}{:layer 94,95} A()
  ensures{:atomic} |{ A: return true; }|;
{
  yield;
}

procedure{:yields}{:layer 95,95} P()
{
  yield;
  par A() | H();
  yield;
}
