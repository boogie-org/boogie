// RUN: %boogie -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,1} x:int;

procedure {:yield_invariant} {:layer 1} yield_x(n: int);
requires {:layer 1} x >= n;

procedure {:yields} {:layer 1} p()
requires {:layer 1} x >= 5;
ensures  {:layer 1} x >= 8;
{
  call yield_x(x);
  call Incr(1);
  call yield_x(x);
  call Incr(1);
  call yield_x(x);
  call Incr(1);
  call yield_x(x);
}

procedure {:yields} {:layer 1} q()
{
  yield;
  call Incr(3);
  yield;
}

procedure {:atomic} {:layer 1,1} AtomicIncr(val: int)
modifies x;
{
  x := x + val;
}

procedure {:yields} {:layer 0} {:refines "AtomicIncr"} Incr(val: int);
