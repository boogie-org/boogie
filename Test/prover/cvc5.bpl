// RUN: %boogie /trace /proverOpt:SOLVER=cvc5 "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK: \[TRACE\] Using prover:.*cvc5
// CHECK: Boogie program verifier finished with 1 verified, 0 errors

procedure P(x: int, y: int) {
  assert x*y == y*x;
}
