// RUN: %parallel-boogie /proverOpt:PROVER_PATH=/usr/bin/false "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure P(x: int, y: int) {
  assert x*y == y*x;
}
