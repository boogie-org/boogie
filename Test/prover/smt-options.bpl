// RUN: %boogie /proverLog:"%t.smt2" "%s"
// RUN: %OutputCheck --file-to-check "%t.smt2" "%s"
// CHECK: (set-option :smt.arith.solver 2)
// CHECK: (set-option :smt.case_split 2)
procedure
{:smt_option "smt.arith.solver", 2}
{:smt_option "smt.case_split", 2}
P1(a: int, b: int) {
  assert (a + b) - (a * b) == (b + a) - (a * b);
}
