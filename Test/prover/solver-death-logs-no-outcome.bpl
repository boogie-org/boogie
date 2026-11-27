// The log of a check whose solver died records no outcome for it.
// RUN: %boogie /proverOpt:PROVER_PATH=/usr/bin/false /proverLog:"%t.smt2" "%s" | %OutputCheck "%s"
// RUN: ! grep "; Valid" "%t.smt2"
// CHECK-L: Verification encountered solver exception (P)

procedure P() {
  assert true;
}
