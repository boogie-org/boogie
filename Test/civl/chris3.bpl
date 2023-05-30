// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

atomic action {:layer 95} skip() { }

yield procedure {:layer 94} H()
refines skip;
{
}

yield procedure {:layer 94} A()
refines skip;
{
}

yield procedure {:layer 95} P()
{
  par A() | H();
}
