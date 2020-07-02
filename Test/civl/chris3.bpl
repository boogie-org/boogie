// RUN: %boogie -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure{:atomic}{:layer 95} skip() { }

procedure{:yields}{:layer 94} {:refines "skip"} H()
{
}
  
procedure{:yields}{:layer 94} {:refines "skip"} A()
{
}

procedure{:yields}{:layer 95} P()
{
  par A() | H();
}
