// RUN: %parallel-boogie -infer:j "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The interval domain reads a negated guard only in its reversed form, both as a constraint and for its
// widening thresholds. One test is over real and one over int, the two types whose guards are reversed.

// The only source of "3.0 <= r" is the first loop's exit edge, and r is reassigned in a second loop,
// so the fact has to survive as an inferred invariant at the second loop head.
procedure Constraint()
{
  var r: real;
  var k: int;
  r := 0.0;
  while (r < 3.0) { r := r + 1.0; }
  k := 0;
  while (k < 2) { r := r + 1.0; k := k + 1; }
  assert 3.0 <= r;
}

// The only source of the bound is the widening threshold that the else branch's "100 >= b" provides; the
// assertion names its bound through a constant, which yields no threshold.
const N: int;
axiom N == 101;

procedure Threshold()
{
  var b: int;
  b := 0;
  while (*)
  {
    assert b <= N;
    if (b > 100) { b := 0; } else { b := b + 1; }
  }
}
