// RUN: %boogie -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,3} x: int;

procedure {:right} {:layer 1} AtomicIncr()
modifies x;
{ x := x + 1; }

procedure {:yields} {:layer 0} {:refines "AtomicIncr"} Incr();

procedure {:right} {:layer 2} AtomicIncr2()
modifies x;
{ x := x + 2; }

procedure {:yields} {:layer 1} {:refines "AtomicIncr2"} Incr2()
{
  par Incr() | Incr();
}

procedure {:yield_invariant} {:layer 1} Yield();

procedure {:atomic} {:layer 3} AtomicIncr4()
modifies x;
{ x := x + 4; }

procedure {:yields} {:layer 2} {:refines "AtomicIncr4"} Incr4()
{
  par Incr2() | Incr2() | Yield();
}



