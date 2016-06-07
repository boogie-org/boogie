// RUN: %boogie -noinfer -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure{:layer 1}{:extern} P() returns(i:int);

procedure{:yields}{:layer 1,1}{:extern} Y({:layer 1}x:int);

procedure{:yields}{:layer 1,2} A({:layer 1}y:int)
  ensures {:atomic} |{ A: return true; }|;
{
  var{:layer 1} tmp:int;
  call Y(y);
  call tmp := P();
  call Y(tmp);
}
