// RUN: %parallel-boogie -proverOpt:PROVER_PATH=bogus-path "%s" | %OutputCheck "%s"

procedure foo() {}
// CHECK-L: Advisory: foo SKIPPED because: One or more errors occurred. (Cannot find specified prover: bogus-path)
