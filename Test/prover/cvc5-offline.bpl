// RUN: %boogie /trace /proverOpt:BATCH_MODE=true /proverLog:cvc5-offline.smt2 "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK: Boogie program verifier finished with 1 verified, 0 errors
// RUN: cvc5 --incremental cvc5-offline.smt2

procedure P(x: int, y: int) {
  assert x*y == y*x;
}
