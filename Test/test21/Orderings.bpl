

const a, b:int;
const c:int extends a, b;

procedure P() returns () {
  var x:int;

  assert c <: a;

  assume c <: x && x <: a;
  assert x == c || a == x;

  assert x == b;             // should not be provable
}

procedure Q() returns () {
  assume b <: a;
  assert b == a;
}