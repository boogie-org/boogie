// A solver that exits while Boogie waits for its answer fails the check that used it, but leaves neither that check
// nor the next one waiting forever.
// RUN: %boogie /proverOpt:C:"-T:1" "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK-L: Verification encountered solver exception (Cubes1)
// CHECK-L: Verification encountered solver exception (Cubes2)
// CHECK-L: Boogie program verifier finished with 0 verified, 0 errors, 2 solver exceptions

// z3 decides neither assertion before its hard time limit of a second makes it exit.
procedure Cubes1(x: int, y: int, z: int) {
  assume x > 1 && y > 1 && z > 1;
  assert x * x * x + y * y * y != z * z * z;
}

procedure Cubes2(x: int, y: int, z: int) {
  assume x > 2 && y > 2 && z > 2;
  assert x * x * x + y * y * y != z * z * z;
}
