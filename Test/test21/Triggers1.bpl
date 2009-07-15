


function f<a>(a) returns (bool);
function g(int) returns (bool);

axiom (forall x:int :: f(x));
axiom (forall x:int :: g(x));

procedure P() returns () {
  var x : int, m : [int]int;
  assert f(x);
  assert f(m[x]);
  assert g(x);
  assert g(m[x]);
  assert f(true);   // should not be provable
}