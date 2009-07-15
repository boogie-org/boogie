

function f(int) returns (int);
axiom f(13) == 0;

procedure P() returns () {
  assert (exists f:int :: 0 == f(f));
}