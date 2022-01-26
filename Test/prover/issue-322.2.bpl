// RUN: %parallel-boogie -proverOpt:bogus-option "%s" | %OutputCheck "%s"

procedure foo() {}
// CHECK-L: Fatal Error: ProverException: Unrecognised prover option: bogus-option
