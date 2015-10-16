// RUN: %boogie -noinfer -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var{:layer 1,1} x:int;

procedure{:layer 1}{:extern} P1(i:int);
procedure{:pure}{:extern} P2(j:int);

procedure{:yields}{:layer 1,2} A1({:layer 1}i:int)
  ensures {:atomic} |{ A: return true; }|;
{
  yield;
  call P1(i);
  call P2(i);
  yield;
}
