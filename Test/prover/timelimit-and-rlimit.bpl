// RUN: %boogie /proverLog:"%t.smt2" "%s"
// RUN: %OutputCheck --file-to-check "%t.smt2" "%s"
// CHECK: (set-option :timeout 1000)
// CHECK: (set-option :rlimit 10000)
procedure
{:timeLimit 1}
{:rlimit 10000}
P1(a: int, b: int) {
  assert (a + b) - (a * b) == (b + a) - (a * b);
}
