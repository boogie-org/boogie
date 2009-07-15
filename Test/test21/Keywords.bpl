

function NOT(x:int) returns(int);

axiom (forall x:int :: NOT(x) == 1 - x);

procedure P() returns () {
  assert NOT(5) == -4;
}