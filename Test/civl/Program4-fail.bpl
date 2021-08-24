// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,1} x:int;

procedure {:yield_invariant} {:layer 1} yield_x(n: int);
requires x >= n;

procedure {:yields} {:layer 1}
{:yield_requires "yield_x", 5}
{:yield_ensures "yield_x", 8}
p1()
{
  call Incr(1);
  call Incr(1);
  call Incr(1);
}

procedure {:yields} {:layer 1}
// {:yield_requires "yield_x", x}       // Without this precondition, the usage of old(.) in the postcondition is not sound.
{:yield_ensures "yield_x", old(x) + 3}
p2()
{
  call Incr(1);
  call Incr(1);
  call Incr(1);
}

procedure {:yields} {:layer 1} q()
{
  call Incr(3);
}

procedure {:both} {:layer 1,1} AtomicIncr(val: int)
modifies x;
{
  x := x + val;
}

procedure {:yields} {:layer 0} {:refines "AtomicIncr"} Incr(val: int);
