// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,1} x:int;

procedure {:yield_invariant} {:layer 1} yield_x(n: int);
requires x >= n;

procedure {:yields} {:layer 1}
{:yield_requires "yield_x", 5}
{:yield_ensures "yield_x", 8}
p()
{
  call Incr(1);
  call yield_x(x);
  call Incr(1);
  call yield_x(x);
  call Incr(1);
}

procedure {:yields} {:layer 1} q()
{
  call Incr(3);
}

procedure {:atomic} {:layer 1,1} AtomicIncr(val: int)
modifies x;
{
  x := x + val;
}

procedure {:yields} {:layer 0} {:refines "AtomicIncr"} Incr(val: int);
