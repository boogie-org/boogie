// RUN: %boogie -noinfer -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var{:layer 1,1} g:int;

procedure{:layer 1} P(x:int)
  requires {:layer 1} x == 0;
{
}

procedure{:yields}{:layer 1,2} Y(x:int)
  ensures{:atomic} |{ A: return true; }|;
{
  yield;
  
  call P(x);
  assert{:layer 1} x == 0;

  yield;
}
