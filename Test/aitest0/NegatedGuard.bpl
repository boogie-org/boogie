// RUN: %parallel-boogie -infer:j "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The interval domain learns from the negation of an int or real guard, both as a constraint and as a
// widening threshold.

// The only source of "3.0 <= r" is the first loop's exit edge, and r is reassigned in a second loop,
// so the fact has to survive as an inferred invariant at the second loop head. The bound is a variable
// so that the exit edge assumes "!(r < n)" rather than "n <= r".
procedure Constraint()
{
  var r, n: real;
  var k: int;
  r := 0.0;
  n := 3.0;
  while (r < n) { r := r + 1.0; }
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
