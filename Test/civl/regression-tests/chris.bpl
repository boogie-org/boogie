// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var{:layer 1,3} x:int;

yield procedure {:layer 2} Havoc()
{
}

atomic action {:layer 2,3} AtomicRecover()
{ assert x == 5; }

yield procedure {:layer 1} Recover()
refines AtomicRecover;
{
}

yield procedure {:layer 3} P()
preserves call Inv();
{
  call Havoc();
  call Inv();
  call Recover();
}

yield invariant {:layer 3} Inv();
preserves x == 5;
