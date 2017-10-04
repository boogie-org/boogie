// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure{:yields}{:layer 94} H()
{
  yield;
}

procedure{:atomic}{:layer 95} atomic_A() { }
  
procedure{:yields}{:layer 94} {:refines "atomic_A"} A()
{
  yield;
}

procedure{:yields}{:layer 95} P()
{
  yield;
  par A() | H();
  yield;
}
