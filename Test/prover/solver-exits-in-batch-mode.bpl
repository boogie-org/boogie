// A solver that exits without answering is reported as dead instead of being waited for forever.
// RUN: %boogie /proverOpt:BATCH_MODE=true /proverOpt:PROVER_PATH=silent-solver.sh "%s" | %OutputCheck "%s"
// CHECK-L: Fatal Error: ProverException: Prover died with no further output, perhaps it ran out of memory or was killed.

procedure P(x: int) {
  assert x > 0;
}
