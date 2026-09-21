// RUN: %parallel-boogie -infer:j -instrumentInfer:e -printInstrumented -noVerify "%s" > "%t"
// RUN: %OutputCheck "--file-to-check=%t" "%s"
// CHECK-NOT-L: <= p

// Pow bounded the power by the bounds of its *exponent*: Lo was one for a nonzero exponent and Hi was the
// exponent's own upper bound. Neither follows -- 3.0 ** 2.0 is 9.0, above the exponent's bound of 2.0 --
// so the rule is gone and no bound on the power is inferred.
//
// Unlike the other rules this one cannot be caught by a false assertion: "**" is emitted as real_pow,
// which no prover declares, so any program whose verification condition mentions it dies in the solver.
// The inferred invariant is therefore checked directly, with -noVerify.

procedure PowBounds(x: real, y: real) returns (p: real)
{
  var i: int;

  assume 0e0 <= x;
  assume 1e0 <= y && y <= 2e0;
  p := x ** y;
  i := 0;
  while (i < 3) { i := i + 1; }
}
