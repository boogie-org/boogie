// RUN: boogie "-proverOpt:O:smt.arith.solver=2" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file tests issue https://github.com/boogie-org/boogie/issues/321

procedure Test(a: int, b: int)
  requires 1 <= a;
  requires 1 <= b;
{
  // the following line once caused a "Prover error: Unexpected prover response"
  assert a <= a * b;
}
