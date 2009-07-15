

const b:int;
const a:int extends b complete;

const c:int extends a;
const d:int extends a;

procedure P() returns () {
  var x:int;

  assert c <: b && d <: a;

  assume x <: a && !(x <: c) && x != a;
  assert x <: d;

  assert b <: x;            // should not be provable
}