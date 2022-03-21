// RUN: %boogie /trace /proverOpt:BATCH_MODE=true "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK: \[TRACE\] Running in batch mode.
// CHECK: Boogie program verifier finished with 1 verified, 0 errors

procedure P(x: int, y: int) {
  assert x*y == y*x;
}
