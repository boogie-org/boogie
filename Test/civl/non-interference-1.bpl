// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,1} g:int;

yield procedure {:layer 1} PB()
{
  call Incr();
}

action {:layer 1} AtomicIncr()
modifies g;
{ g := g + 1; }

yield procedure {:layer 0} Incr();
refines AtomicIncr;

action {:layer 1} AtomicSet(v: int)
modifies g;
{ g := v; }

yield procedure {:layer 0} Set(v: int);
refines AtomicSet;

yield invariant {:layer 1} Yield();
invariant g == 3;

yield procedure {:layer 1} PC()
ensures call Yield();
{
  call Set(3);
}

yield procedure {:layer 1} PE()
{
  call PC();
}

yield procedure {:layer 1} PD()
{
  call PC();
  assert {:layer 1} g == 3;
}

yield procedure {:layer 1} Main()
{
  while (*)
  {
    async call PB();
    async call PE();
    async call PD();
  }
}
