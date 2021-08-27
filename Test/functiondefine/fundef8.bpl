// RUN: %parallel-boogie  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:define} eqC2<alpha>(x:alpha) returns (bool) { x == 2 }

procedure P() {
  assert eqC2(2, 2);
}
