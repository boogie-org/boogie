// RUN: %parallel-boogie -trace -xml:"%t.xml" "%s"
// Chop off the first line, since OutputCheck expects ASCII and can't handle the byte-order mark
// RUN: tail -n +2 "%t.xml" > "%t.trimmed.xml"
// RUN: %OutputCheck "%s" --file-to-check="%t.trimmed.xml"
// CHECK: \<method name="SomethingTotallyDifferent" startTime=".*"\>

procedure {:displayName "SomethingTotallyDifferent"} OriginalProcedureName()
{
  assert 1 + 1 == 2;
  assert 2 + 2 == 4;
}
