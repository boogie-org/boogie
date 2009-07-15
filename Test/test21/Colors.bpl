

type Color;

const Blue, Red, Green : Color;

axiom (forall x : Color :: x == Blue || x == Red || x == Green);

procedure P() returns () {
  var x : Color;

  assume x != Blue;
  assert x == Red;        // should not be provable
}

procedure Q() returns () {
  var x : Color;

  assume x != Blue && x != Green;
  assert x == Red;
}