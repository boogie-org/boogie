// Don't use %parallel-boogie so the trace output is more predictable
// RUN: %boogie /errorTrace:0 /trace "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"

// CHECK: Verifying DoTheSplitting ...
// CHECK:      checking split 1/11.*
// CHECK:      checking split 2/11.*
// CHECK:      checking split 3/11.*
// CHECK:      --> split #3 done,  \[.* s\] Invalid
// CHECK:      checking split 4/11.*
// CHECK:      checking split 5/11.*
// CHECK:      checking split 6/11.*
// CHECK:      checking split 7/11.*
// CHECK:      checking split 8/11.*
// CHECK:      checking split 9/11.*
// CHECK:      checking split 10/11.*
// CHECK:      checking split 11/11.*
// CHECK-L: SplitOnEveryAssert.bpl(36,5): Error: this assertion could not be proved

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
