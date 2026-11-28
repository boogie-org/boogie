// -xml records a check that ended in a solver exception.
// RUN: %boogie /proverOpt:PROVER_PATH=/usr/bin/false -xml:"%t.xml" "%s" | %OutputCheck "%s"
// RUN: grep 'outcome="solverexception"' "%t.xml"
// CHECK-L: Boogie program verifier finished with 0 verified, 0 errors, 1 solver exceptions

procedure P() {
  assert false;
}
