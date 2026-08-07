// RUN: %parallel-boogie -infer:j "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Abstract interpretation asks a float literal for integer bounds. Exponent sizes are unbounded, so
// those bounds can be enormous: at float24e32 the floor of a large value is a 256 MB integer, and at
// float24e40 it exceeds what BigInteger can represent -- which surfaced here as an unhandled
// OverflowException rather than as a verification result.
//
// -infer:j is what reaches the interval domain; without it these literals are only parsed and printed.

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

// A tiny value at a wide exponent bounds to 0/1 cheaply, so declining the wide case must not have made
// the whole format unusable.
procedure small24e32() returns (r: int) {
  var f: float24e32;
  f := 0x1.0e-536870911f24e32;
  if (f == 0x1.0e-536870911f24e32) { r := 1; } else { r := 0; }
}

// Ordinary formats keep their bounds; this is the behaviour the size limit must leave alone.
procedure ordinary() returns (r: int) {
  var f: float24e8;
  f := 0x1.8e0f24e8;
  if (f == 0x1.8e0f24e8) { r := 1; } else { r := 0; }
}
