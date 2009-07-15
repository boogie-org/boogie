

axiom (forall x:bool :: x || !x);
axiom (forall x:bool :: x == true || x == false);

procedure P() returns () {
  var i : int;
  var j : bool;

  assert i != 3 || i != 4;
  assert j || !j;

  assert false;
}