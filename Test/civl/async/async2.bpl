// RUN: %boogie -noinfer -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,2} x: int;

procedure {:left} {:layer 1,2} AtomicIncr()
modifies x;
{ x := x + 1; }

procedure {:left} {:layer 1,2} AtomicDecr()
modifies x;
{ x := x - 1; }

procedure {:yields} {:layer 0} {:refines "AtomicIncr"} Incr();
procedure {:yields} {:layer 0} {:refines "AtomicDecr"} Decr();

procedure {:yields} {:layer 1} {:refines "AtomicIncr"} AsyncIncr()
{
  yield;
  async call Incr();
  yield;
}

procedure {:yields} {:layer 1} {:refines "AtomicDecr"} AsyncDecr()
{
  yield;
  async call Decr();
  yield;
}

procedure {:yields} {:layer 1} AsyncIncrDecr()
{
  yield;
  async call Incr();
  async call Decr();
  yield;
}
