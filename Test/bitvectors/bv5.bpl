// RUN: %boogie  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure P() returns () {
  var m : <a>[a]int;

  m[23bv5] := 17;
  m[21bv5] := 19;
  m[21bv6] := -3;

  assert m[23bv5] == 17;
  assert m[21bv6] == 3; // should not be provable
}
