// RUN: %boogie "-proverOpt:O:smt.arith.solver=2" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file tests issue https://github.com/boogie-org/boogie/issues/321

procedure Test(a: int, b: int)
  requires 1 <= a;
  requires 1 <= b;
{
  // Ideally, the following line is verified. That's what happens when using
  // Z3 v4.8.5 and Z3 v4.8.8. However, Z3 v4.8.9 instead returns "unknown"
  // stating incomplete arithmetic as the reason, and then *has no model available*.
  // That once caused issues for Boogie. This test, if run with Z3 v.4.8.9,
  // shows that Boogie reports this as an inconclusive test.
  assert a <= a * b;
}
