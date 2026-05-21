// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,1} x:int;

yield invariant {:layer 1} yield_x(n: int);
preserves x >= n;

yield procedure {:layer 1} p()
requires call yield_x(5);
ensures call yield_x(8);
{
  call Incr(1);
  call Incr(1);
  call Incr(1);
}

yield procedure {:layer 1} q()
{
  call Incr(3);
}

both action {:layer 1,1} AtomicIncr(val: int)
modifies x;
{
  x := x + val;
}

yield procedure {:layer 0} Incr(val: int);
refines AtomicIncr;
