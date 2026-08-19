// RUN: %parallel-boogie -infer:j "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The interval domain (-infer:j) asks float literals for integer bounds, which used to crash on floats
// whose exponent makes those bounds huge.

procedure large24e32() returns (r: int) {
  var f: float24e32;
  f := 0x1.0e536870911f24e32;
  if (f == 0x1.0e536870911f24e32) { r := 1; } else { r := 0; }
}

procedure large24e40() returns (r: int) {
  var f: float24e40;
  f := 0x1.0e137438953471f24e40;
  if (f == 0x1.0e137438953471f24e40) { r := 1; } else { r := 0; }
}

// A small value in a wide format still gets its bounds
procedure small24e32() returns (r: int) {
  var f: float24e32;
  f := 0x1.0e-536870911f24e32;
  if (f == 0x1.0e-536870911f24e32) { r := 1; } else { r := 0; }
}

// Ordinary formats are unaffected
procedure ordinary() returns (r: int) {
  var f: float24e8;
  f := 0x1.8e0f24e8;
  if (f == 0x1.8e0f24e8) { r := 1; } else { r := 0; }
}
