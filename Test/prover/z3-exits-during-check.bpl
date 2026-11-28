// A solver that runs out of its own hard time limit answers `timeout` and exits 0, so the check that asked it
// times out rather than losing its solver.
// RUN: %boogie /proverOpt:C:"-T:1" /trace "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK: .*solver resource count: -1, 1 proof obligation\]  error
// CHECK-L: Error: this assertion could not be proved
// CHECK-L: Error: this assertion could not be proved
// CHECK-L: Boogie program verifier finished with 0 verified, 2 errors

// z3 decides neither assertion before its hard time limit of a second makes it exit.
procedure Cubes1(x: int, y: int, z: int) {
  assume x > 1 && y > 1 && z > 1;
  assert x * x * x + y * y * y != z * z * z;
}

// Checked only if the failed check above gives up its place in the checker pool.
procedure Cubes2(x: int, y: int, z: int) {
  assume x > 1 && y > 1 && z > 1;
  assert x * x * x + y * y * y != z * z * z;
}
