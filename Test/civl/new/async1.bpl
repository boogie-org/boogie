// RUN: %boogie -noinfer -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,2} x: int;

procedure {:left} {:layer 1} AtomicIncr()
modifies x;
{ x := x + 1; }

procedure {:yields} {:layer 0} {:refines "AtomicIncr"} Incr();

procedure {:left} {:layer 2} AtomicAsyncIncr()
modifies x;
{ x := x + 1; }

procedure {:yields} {:layer 1} {:refines "AtomicAsyncIncr"} AsyncIncr()
{
  yield;
  async call Incr();
  yield;
}