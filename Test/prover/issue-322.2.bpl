// RUN: %parallel-boogie -proverOpt:bogus-option "%s" | %OutputCheck "%s"

procedure foo() {}
// CHECK-L: Advisory: foo SKIPPED because: One or more errors occurred. (Unrecognised prover option: bogus-option)
