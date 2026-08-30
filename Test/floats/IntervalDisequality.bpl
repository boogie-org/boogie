// RUN: %parallel-boogie -infer:j "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Why the domain describes no float: see IntervalNoFloatTracked.bpl, which pins that property directly.
// This file pins one consequence of it.

// Excluding one value from an interval moves an endpoint only when the values are integers. For a float
// it leaves the bounds where they were.

procedure Disequality()
{
  var z: float24e8;
  var i: int;

  havoc z;
  assume 0x1.0e0f24e8 <= z;
  if (z != 0x1.8e0f24e8)
  {
    i := 0;
    while (i < 3) { i := i + 1; }
    assert 0x2.0e0f24e8 <= z;  // z can be 1.25
  }
}
