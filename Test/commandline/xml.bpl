// RUN: %parallel-boogie -randomSeed:0 -xml:"%t-1.xml" "%s"
// RUN: %parallel-boogie -randomSeed:0 -xml:"%t-2.xml" "%s"
// RUN: grep -Eo "resourceCount=\"[0-9]+\"" "%t-1.xml" | sort -g > "%t-res1"
// RUN: grep -Eo "resourceCount=\"[0-9]+\"" "%t-2.xml" | sort -g > "%t-res2"
// RUN: diff "%t-res1" "%t-res2"
// Chop off the first line, since OutputCheck expects ASCII and can't handle the byte-order mark
// RUN: tail -n +2 "%t-1.xml" > "%t.trimmed.xml"
// RUN: %OutputCheck "%s" --file-to-check="%t.trimmed.xml"
// We only check for one of the methods in the XML because there's no
// guarantee about what order they'll appear in.
// CHECK: \<method name="ExampleWithSplits" startTime=".*"\>
// CHECK:   \<assertionBatch number="1" startTime=".*"\>
// CHECK:     \<assertion file="xml.bpl" line="25" column="3" /\>
// CHECK:     \<conclusion duration=".*" outcome="valid" resourceCount=".*" /\>
// CHECK:   \</assertionBatch\>
// CHECK:   \<assertionBatch number="2" startTime=".*"\>
// CHECK:     \<assertion file="xml.bpl" line="27" column="3" /\>
// CHECK:     \<conclusion duration=".*" outcome="valid" resourceCount=".*" /\>
// CHECK:   \</assertionBatch\>
// CHECK:   \<conclusion endTime=".*" duration=".*" resourceCount=".*" outcome="correct" /\>
// CHECK: \</method\>

procedure ExampleWithSplits()
{
  assert 1 + 1 == 2;
  assume {:split_here} true;
  assert 2 + 2 == 4;
}

procedure ExampleWithoutSplits()
{
  assert 1 + 1 == 2;
  assert 2 + 2 == 4;
}

procedure AnotherExampleWithoutSplits()
{
  assert 1 + 1 == 2;
  assert 2 + 2 == 4;
}
