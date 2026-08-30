// RUN: %parallel-boogie -infer:j "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Why the domain describes no float: see IntervalNoFloatTracked.bpl, which pins that property directly.
// This file pins one consequence of it.

// From "lit < v" the domain took the next integer up, which is right for an int and wrong for a float:
// the excluded value is the bound itself.

procedure StrictBound()
{
  var z: float24e8;
  var i: int;

  havoc z;
  if (0x1.0e0f24e8 < z)
  {
    i := 0;
    while (i < 3) { i := i + 1; }
    assert 0x2.0e0f24e8 <= z;  // z can be 1.5
  }
}
