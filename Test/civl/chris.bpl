// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var{:layer 1} x:int;

procedure{:yields}{:layer 2} Havoc()
  ensures{:atomic} |{ A: return true; }|;
{
  yield;
}

procedure{:yields}{:layer 1} Recover()
  ensures{:atomic} |{ A: assert x == 5; return true; }|;
{
  yield;
}

procedure{:yields}{:layer 3} P()
  ensures{:atomic} |{ A: return true; }|;
  requires{:layer 2,3} x == 5;
  ensures {:layer 2,3} x == 5;
{

  yield; assert{:layer 2,3} x == 5;
  call Havoc();
  yield; assert{:layer 3} x == 5;
  call Recover();
  yield; assert{:layer 2,3} x == 5;
}
