// RUN: %parallel-boogie "-proverOpt:O:smt.arith.solver=2" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file contains the Boogie input reported in issue https://github.com/boogie-org/boogie/issues/321.
// Boogie once had two problems with this input.
//
// ** The simpler problem is that Z3 v4.8.9 responds with "unknown" and says:
//      (:reason-unknown "smt tactic failed to show goal to be sat/unsat (incomplete (theory arithmetic))")
//    This response is now being handled by Boogie in the same way as some other
//    incomplete responses (e.g., incomplete quantifiers, or the similar response
//    of just (:reason-unknown "(incomplete (theory arithmetic))"), see Incomplete-RealTypes.bpl).
//
// ** The more difficult problem is that Z3 v4.8.9 does not give a model after responding
//    with the :reason-unknown above. Without a model, Boogie cannot give a precise error
//    message. Instead, Boogie now outputs:
//
//        Prover error: line 31 column 30: model is not available
//
//        IncompleteArithmetic-git-issue-321.bpl(10,11): Verification inconclusive (Test)
//
//        Boogie program verifier finished with 0 verified, 0 errors, 1 inconclusive
//
//    A future improvement to Boogie would be to try to replace the first two lines above with
//    something like:
//
//        IncompleteArithmetic-git-issue-321.bpl(10,11): Verification inconclusive (model is not available) (Test)
//
// Note that we have detected this problem only when using Z3 v4.8.9 and smt.arith.solver=2.
// For example, when using Z3 v4.8.8, or when using Z3 v4.8.9 and smt.arith.solver=6,
// Z3 proves the assertion below, so there is no error for Boogie to report.
// At the moment, Boogie's CI uses Z3 v4.8.8. Therefore, the .expect file for this test says
//
//     Boogie program verifier finished with 1 verified, 0 errors
//
// instead of the output mentioned above. Because Z3 v4.8.8 is used, this test file
// doesn't actually test either of the two problems above. If Boogie's CI ever changes to
// use Z3 v4.8.9 (or, perhaps, to use multiple provers of multiple versions), then the output
// mentioned above is the expected one.
//
// Meanwhile, see IncompleteArithmetic-RealTypes.bpl, which tests Boogie's treatment of a related
// Z3 output.
//
// Future version of Z3 will have a have an option "candidate_models", see
//   https://github.com/Z3Prover/z3/issues/4924
// and
//   https://github.com/Z3Prover/z3/commit/f519c58acec47c11c64eab4a145f8735fa63a6e6
// With that option set to true, Boogie can expect a model to always be available when Z3 reports
// "unknown". That would be a good option for Boogie to set when using a version of Z3 that
// supports it.

procedure Test(a: int, b: int)
  requires 1 <= a;
  requires 1 <= b;
{
  // Ideally, the following line is verified. That's what happens when using
  // Z3 v4.8.5 and Z3 v4.8.8. However, Z3 v4.8.9 instead returns "unknown"
  // stating incomplete arithmetic as the reason, and then *has no model available*.
  assert a <= a * b;
}
