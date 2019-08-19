// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure main() returns () {
  var x : float53e11;
  var y : float53e11;
  var z : float53e11;
  var r : float53e11;
  x := 0x1.0e10f53e11;
  y := x + 0x1.0e0f53e11;
  z := x - 0x1.0e0f53e11;
  r := y - z;
  
  assert r == 0x2.0e0f53e11;
}
