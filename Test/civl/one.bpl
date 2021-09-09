// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,1} x:int;

procedure {:atomic} {:layer 1} AtomicSet(v: int)
modifies x;
{ x := v; }

procedure {:yields} {:layer 0} {:refines "AtomicSet"} Set(v: int);

procedure {:yields} {:layer 1} B()
ensures {:layer 1} x == 5;
{
  call Set(5);
}
