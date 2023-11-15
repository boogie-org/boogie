// RUN: %boogie /proverLog:"%t.smt2" "%s"
// RUN: %OutputCheck --file-to-check "%t.smt2" "%s"
// CHECK: (set-option :smt.arith.solver 2)
// CHECK: (set-option :smt.arith.solver 6)
// CHECK: (set-option :sat.smt.proof.check true)
procedure
{:smt_option "smt.arith.solver", 2}
P1(a: int, b: int) {
  assert (a + b) - (a * b) == (b + a) - (a * b);
}

procedure
{:smt_option "smt.arith.solver", 6}
{:smt_option "sat.smt.proof.check", true}
P2(a: int, b: int) {
  assert (a + b) - (a * b) == (b + a) - (a * b);
}
