// RUN: %boogie /trace /proverOpt:PROVER_PATH=mocksolver.sh "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK: resource count: -1

procedure P(x: int, y: int) {
  assert x*y == y*x;
}
