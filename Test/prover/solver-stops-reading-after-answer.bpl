// A solver that stops reading once it has answered still has its answer reported, although Boogie writes to it
// after the answer.
// RUN: %boogie /proverOpt:PROVER_PATH=answers-then-stops-reading.sh "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK-L: Boogie program verifier finished with 1 verified, 0 errors

// Batch mode sends nothing after the answer.
// UNSUPPORTED: batch_mode

procedure P(x: int) {
  assert x == x;
}
