// RUN: %parallel-boogie -infer:j "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Mul had a branch for two negative lower bounds that claimed Hi = lo0 * lo1, deriving an upper bound
// from two lower bounds. It holds only if both operands are also bounded above by zero, which nothing
// established. The real form is reachable from Dafny, which emits `*` on reals natively and enables this
// analysis unconditionally, and there it proves `false`.
//
// Each product is computed in a loop because an inferred fact reaches the prover at a loop head.

procedure MulInt(x: int, y: int)
  requires -3 <= x;
  requires -3 <= y;
{
  var z: int;
  var i: int;

  z := x * y;
  i := 0;
  while (i < 3) { z := x * y; i := i + 1; }
  assert z < 10;   // x == y == 1000 gives 1000000
}

procedure MulReal(r: real, s: real)
  requires -3e0 <= r;
  requires -3e0 <= s;
{
  var d: real;
  var i: int;

  d := r * s;
  i := 0;
  while (i < 3) { d := r * s; i := i + 1; }
  assert d <= 9e0;  // r == s == 1000.0 gives 1000000.0
}
