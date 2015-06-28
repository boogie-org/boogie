// RUN: %boogie  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure Q() returns () {
  var x : bv32, y : bv16;

  x := y ++ y;
  assert x[16:0] == y;
  assert x == x[16:0] ++ y;
  assert x[17:1] == y;     // should not be verifiable
}
