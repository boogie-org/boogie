// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,1} x:int;

procedure {:atomic} {:layer 1} AtomicSet(v: int)
modifies x;
{ x := v; }

procedure {:yields} {:layer 0} {:refines "AtomicSet"} Set(v: int);

procedure {:yields} {:layer 1} B()
{
  yield;
  call Set(5);
  yield;
  assert {:layer 1} x == 5;
}

