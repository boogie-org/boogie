// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function {:inline true} foo(x:int) returns(bool)
  { x > 0 }

procedure P() {
  assert foo(13);
  assert foo(-5);  // error
}
