// RUN: %parallel-boogie -infer:j "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Div, Mod and RealDiv bounded their result whenever both operands had a lower bound of at least zero,
// which admits a zero divisor. Division and mod by zero are underspecified in SMT-LIB, so the result is
// an arbitrary value and no bound holds of it. Each rule now requires a divisor of at least one.
//
// Each quotient is computed in a loop because an inferred fact reaches the prover at a loop head.

procedure IntDiv(a: int)
  requires 0 <= a;
{
  var q: int;
  var i: int;

  q := a div 0;
  i := 0;
  while (i < 3) { q := a div 0; i := i + 1; }
  assert 0 <= q;
}

procedure IntMod(a: int)
  requires 0 <= a;
{
  var m: int;
  var i: int;

  m := a mod 0;
  i := 0;
  while (i < 3) { m := a mod 0; i := i + 1; }
  assert m == 0;
}

procedure RealDiv(r: real)
  requires 0e0 <= r;
{
  var d: real;
  var i: int;

  d := r / 0e0;
  i := 0;
  while (i < 3) { d := r / 0e0; i := i + 1; }
  assert 0e0 <= d;
}
