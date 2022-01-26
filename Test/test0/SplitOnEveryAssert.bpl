// Don't use %parallel-boogie so the trace output is more predictable
// RUN: %boogie /errorTrace:0 /trace "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"

// CHECK:      checking split 1/12, .*
// CHECK:      checking split 2/12, .*
// CHECK:      checking split 3/12, .*
// CHECK:      checking split 4/12, .*
// CHECK:      --> split #4 done,  \[.* s\] Invalid
// CHECK:      checking split 5/12, .*
// CHECK:      checking split 6/12, .*
// CHECK:      checking split 7/12, .*
// CHECK:      checking split 8/12, .*
// CHECK:      checking split 9/12, .*
// CHECK:      checking split 10/12, .*
// CHECK:      checking split 11/12, .*
// CHECK:      checking split 12/12, .*
// CHECK: Verifying DoTheSplitting ...
// CHECK-L: SplitOnEveryAssert.bpl(37,5): Error: This assertion might not hold.

// Verify the second procedure is NOT split. .* is necessary to match the blank line in-between.
// CHECK-NEXT: .*
// CHECK-NEXT: Verifying DontDoTheSplitting ...
// CHECK-NEXT:   \[.* s, solver resource count: .*, .* proof obligations\]  verified

procedure {:vcs_split_on_every_assert} DoTheSplitting() returns (y: int)
  ensures y >= 0;
{
  var x: int;
  x := 5;
  y := 0;
  while (x > 0)
    invariant x + y == 5;
    invariant x*x <= 25;
  {
    x := x - 1;
    assert (x+y) * (x+y) > 25;
    y := y + 1;
    if (x < 3) {
      assert 2 < 2;
      assert y*y > 4;
    }
    else {
      assert y*y*y < 8;
      assert 2 < 2;
    }
    assert (x+y) * (x+y) == 25;
  }
}

procedure DontDoTheSplitting()
{
  assert 1 + 1 == 2;
  assert 2 + 2 == 4;
  assert 3 + 3 == 6;
}
