// Test that only two errors are reported, but do not specify which those are.

// RUN: %parallel-boogie /errorLimit:2 "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// XFAIL: *

// CHECK-L: Error: A postcondition might not hold on this return path
// CHECK-L: Error: A postcondition might not hold on this return path
// CHECK-L: Error: A postcondition might not hold on this return path

procedure ManyErrors(x0: int, x1: int, x2: int)
  ensures x0 == 1;
  ensures x1 == 2;
  ensures x2 == 3;
{
}