// RUN: %parallel-boogie -trace "%s" > "%t"
// RUN: %OutputCheck "%s" --file-to-check="%t"
// CHECK: Verifying SomethingTotallyDifferent.*

procedure {:displayName "SomethingTotallyDifferent"} OriginalProcedureName()
{
  assert 1 + 1 == 2;
  assert 2 + 2 == 4;
}
