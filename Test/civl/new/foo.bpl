// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,1} g:int;

procedure {:yields} {:layer 1} PB()
{
  yield;
  call Incr();
  yield;
}

procedure {:atomic} {:layer 1} AtomicIncr()
modifies g;
{ g := g + 1; }

procedure {:yields} {:layer 0} {:refines "AtomicIncr"} Incr();

procedure {:atomic} {:layer 1} AtomicSet(v: int)
modifies g;
{ g := v; }

procedure {:yields} {:layer 0} {:refines "AtomicSet"} Set(v: int);

procedure {:yields} {:layer 1} PC()
ensures {:layer 1} g == 3;
{
  yield;
  call Set(3);
  yield;
  assert {:layer 1} g == 3;
}

procedure {:yields} {:layer 1} PE()
{
  call PC();
}

procedure {:yields} {:layer 1} PD()
{
  call PC();
  assert {:layer 1} g == 3;
}

procedure {:yields} {:layer 1} Main()
{
  yield;
  while (*)
  {
    async call PB();
    yield;
    async call PE();
    yield;
    async call PD();
    yield;
  }
  yield;
}
