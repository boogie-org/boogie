// RUN: %parallel-boogie -trace -xml:"%t.xml" "%s"
// RUN: %OutputCheck "%s" --file-to-check="%t.xml"
// CHECK: \<method name="SomethingTotallyDifferent" startTime=".*"\>

procedure {:displayName "SomethingTotallyDifferent"} OriginalProcedureName()
{
  assert 1 + 1 == 2;
  assert 2 + 2 == 4;
}
