// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,3} x: int;

right action {:layer 1} AtomicIncr()
modifies x;
{ x := x + 1; }

yield procedure {:layer 0} Incr();
refines AtomicIncr;

right action {:layer 2} AtomicIncr2()
modifies x;
{ x := x + 2; }

yield procedure {:layer 1} Incr2()
refines AtomicIncr2;
{
  call Incr() | Incr();
}

yield invariant {:layer 1} Yield();

atomic action {:layer 3} AtomicIncr4()
modifies x;
{ x := x + 4; }

yield procedure {:layer 2} Incr4()
refines AtomicIncr4;
{
  call Incr2() | Incr2() | Yield();
}
