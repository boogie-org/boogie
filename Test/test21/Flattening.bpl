

function g(int) returns (int);
function f(bool) returns (int);


axiom (f((exists x:int :: g(x) >= 12)) == 3);
axiom (f((exists x:int :: g(f((forall y:int :: g(x+y) >= 0))) >= 12)) == 3);


procedure P() returns () {
  assert false;
}