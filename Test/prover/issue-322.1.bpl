// RUN: %parallel-boogie -proverOpt:PROVER_PATH=bogus-path "%s" | %OutputCheck "%s"

procedure foo() {}
// CHECK-L: Fatal Error: ProverException: Cannot find specified prover: bogus-path
