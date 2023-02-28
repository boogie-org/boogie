// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,1} g:int;

procedure {:yields} {:layer 1} PB()
{
  call Incr();
}

procedure {:atomic} {:layer 1} AtomicIncr()
modifies g;
{ g := g + 1; }

procedure {:yields} {:layer 0} {:refines "AtomicIncr"} Incr();

procedure {:atomic} {:layer 1} AtomicSet(v: int)
modifies g;
{ g := v; }

procedure {:yields} {:layer 0} {:refines "AtomicSet"} Set(v: int);

procedure {:yield_invariant} {:layer 1} Yield();
requires g == 3;

procedure {:yields} {:layer 1} {:yield_ensures "Yield"} PC()
{
  call Set(3);
}

procedure {:yields} {:layer 1} PD()
{
  call PC();
  assert {:layer 1} g == 3;
}

procedure {:yields} {:layer 1} Main()
{
  while (*)
  invariant {:yields 1} true;
  {
    par PB() | PC() | PD();
  }
}
