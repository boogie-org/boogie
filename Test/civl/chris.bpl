// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var{:layer 1,3} x:int;

procedure{:yields}{:layer 2} Havoc()
{
}

procedure{:atomic}{:layer 2,3} AtomicRecover()
{ assert x == 5; }

procedure{:yields}{:layer 1} {:refines "AtomicRecover"} Recover()
{
}

procedure{:yields}{:layer 3}{:yield_preserves "Inv"} P()
{
  call Havoc();
  call Inv();
  call Recover();
}

procedure {:yield_invariant} {:layer 3} Inv();
requires x == 5;