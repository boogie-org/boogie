// RUN: %boogie -useArrayTheory "%s" > "%t"
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

procedure{:yields}{:layer 3} P()
  requires{:layer 2,3} x == 5;
  ensures {:layer 2,3} x == 5;
{

  call Havoc();
  yield; assert{:layer 3} x == 5;
  call Recover();
}
