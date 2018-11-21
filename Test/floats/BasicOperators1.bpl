// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure main() returns () {
  var x : float24e8;
  var y : float24e8;
  var z : float24e8;
  
  z := x + y;
  z := x - y;
  z := x * y;
  assume(!FEQ(y, 0x0.0e0f24e8));
  z := x / y;
  
  z := (0x1.0e0f24e8 + 0x1.0e0f24e8 + 0x0.0e0f24e8);
  assert(z == 0x2.0e0f24e8);
  
  z := 0x2.0e0f24e8 - 0x1.0e0f24e8;
  assert(z == 0x1.0e0f24e8);
  
  z := 0x1.0e0f24e8 * 0x1.0e0f24e8;
  assert(z == 0x1.0e0f24e8);
  
  z := 0x1.0e0f24e8 / 0x1.0e0f24e8;
  assert(z == 0x1.0e0f24e8);
  
  return;
}

function {:builtin "fp.eq"} FEQ(float24e8,float24e8) returns (bool);
