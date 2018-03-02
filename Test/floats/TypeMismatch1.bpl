// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure foo(x : float11e5) returns(r : float24e8) {
  var y : float53e11;
  var z : float113e15;
  
  r := x; // Error
  r := y; // Error
  r := z; // Error
  y := x; // Error
  y := z; // Error
  z := x; // Error

  return;
}
