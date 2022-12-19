// RUN: %parallel-boogie -proverOpt:LOG_FILE="%t.smt2" "%s" > "%t"
// RUN: %OutputCheck "--file-to-check=%t.smt2" "%s"
// CHECK-NOT-L: RegEx

procedure P(x: int, y: int) {
  assert x*y == y*x;
}
