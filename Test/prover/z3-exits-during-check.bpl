// A solver that exits while Boogie waits for its answer fails the check that used it, without leaving it waiting
// forever. The second check also has to get a checker from the pool, which the first one used to keep.

// RUN: %boogie /proverOpt:C:"-T:1" "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK-L: Verification encountered solver exception (Cubes1)
// CHECK-L: Verification encountered solver exception (Cubes2)
// CHECK-L: Boogie program verifier finished with 0 verified, 0 errors, 2 solver exceptions

// Batch mode reads z3's `timeout` as a timeout instead, as z3-hard-timeout.bpl expects.
// UNSUPPORTED: batch_mode

// z3 decides neither assertion before its hard time limit of a second makes it exit.
procedure Cubes1(x: int, y: int, z: int) {
  assume x > 1 && y > 1 && z > 1;
  assert x * x * x + y * y * y != z * z * z;
}

procedure Cubes2(x: int, y: int, z: int) {
  assume x > 1 && y > 1 && z > 1;
  assert x * x * x + y * y * y != z * z * z;
}
