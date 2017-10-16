// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure{:atomic}{:layer 95} skip() { }

procedure{:yields}{:layer 94} {:refines "skip"} H()
{
  yield;
}
  
procedure{:yields}{:layer 94} {:refines "skip"} A()
{
  yield;
}

procedure{:yields}{:layer 95} P()
{
  yield;
  par A() | H();
  yield;
}
