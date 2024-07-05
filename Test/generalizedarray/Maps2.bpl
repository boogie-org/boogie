// RUN: %parallel-boogie -lib:base "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type X;
type Y;

procedure bar() {
  var a, b: [X][Y]int;
  var c: [X]bool;
  
  assert MapIte(c, a, b) == MapIte(MapNot(c), b, a);
  assert MapEq(a, b) == MapEq(b, a);
}