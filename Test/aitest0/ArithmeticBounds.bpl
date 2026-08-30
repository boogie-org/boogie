// RUN: %parallel-boogie -infer:j /errorTrace:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Every assertion here can fail. The loops are there because inferred facts reach the prover only at loop
// heads.

// Negative lower bounds on both factors do not bound the product above.
procedure MulInt(x: int, y: int)
  requires -3 <= x;
  requires -3 <= y;
{
  var z: int;
  z := x * y;
  while (*) { }
  assert z <= 9;  // x == y == 4
}

procedure MulReal(x: real, y: real)
  requires -3e0 <= x;
  requires -3e0 <= y;
{
  var z: real;
  z := x * y;
  while (*) { }
  assert z <= 9e0;  // x == y == 4.0
}

// A zero divisor leaves div, mod and / unspecified.
procedure IntDiv(a: int)
  requires 0 <= a;
{
  var q: int;
  q := a div 0;
  while (*) { }
  assert 0 <= q;
}

procedure IntMod(a: int)
  requires 0 <= a;
{
  var m: int;
  m := a mod 0;
  while (*) { }
  assert 0 <= m;
}

procedure RealDiv(r: real)
  requires 0e0 <= r;
{
  var d: real;
  d := r / 0e0;
  while (*) { }
  assert 0e0 <= d;
}
