// RUN: %boogie -noinfer -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure{:extern}{:yields}{:layer 1,2} P1();
  requires{:layer 1} false;
  ensures{:atomic} |{ A: return true; }|;

procedure{:yields}{:layer 2,3} P2()
  ensures{:atomic} |{ A: return true; }|;
{
  assert{:layer 1} false;
  yield;
  call P1();
  yield;
}
