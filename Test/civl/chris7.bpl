// RUN: %boogie -noinfer -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure{:layer 1} P() returns(i:int);

procedure{:yields}{:layer 1} Y({:layer 1}x:int);

procedure{:yields}{:layer 1} A({:layer 1}y:int)
{
  var{:layer 1} tmp:int;
  call Y(y);
  call tmp := P();
  call Y(tmp);
}
