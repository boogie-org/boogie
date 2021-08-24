// RUN: %boogie "%s" > "%t"
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

procedure {:yield_invariant} {:layer 1} PC(old_g: int);
requires g == old_g;

procedure {:yields} {:layer 1} PE()
{
  call PC(g);
}

procedure {:yields} {:layer 1} PD()
{
  call Set(3);
  call PC(g);
  assert {:layer 1} g == 3;
}

procedure {:yields} {:layer 1} Main2()
{
  while (*)
  invariant {:cooperates} {:layer 1} true;
  {
    async call PB();
    async call PE();
    async call PD();
  }
}
