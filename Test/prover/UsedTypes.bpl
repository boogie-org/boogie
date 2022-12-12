// RUN: %parallel-boogie -proverOpt:LOG_FILE="%t.smt2" "%s" > "%t"
// RUN: ! grep RegEx "%t.smt2"

procedure P(x: int, y: int) {
  assert x*y == y*x;
}
