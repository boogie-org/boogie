// A solver that exits between checks is restarted for the next one.
// RUN: %boogie /proverOpt:PROVER_PATH=exits-after-first-check.sh "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK-L: Boogie program verifier finished with 2 verified, 0 errors

// Batch mode starts a solver for every check.
// UNSUPPORTED: batch_mode

procedure P(x: int) {
  assert x == x;
}

procedure Q(x: int) {
  assert x == x;
}
