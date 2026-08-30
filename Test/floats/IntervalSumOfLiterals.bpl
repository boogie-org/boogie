// RUN: %parallel-boogie -infer:j "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Why the domain describes no float: see IntervalNoFloatTracked.bpl, which pins that property directly.
// This file pins one consequence of it.

// Bounds were added the way an int's half-open bounds are added, subtracting one from the upper bound, so
// a float sum produced Lo > Hi -- an inconsistent invariant, which proves anything.

procedure SumOfLiterals()
{
  var z: float24e8;
  var i: int;

  z := 0x1.0e0f24e8 + 0x1.0e0f24e8;
  i := 0;
  while (i < 3)
  {
    z := 0x1.0e0f24e8 + 0x1.0e0f24e8;
    i := i + 1;
  }

  assert false;  // z is 2.0, not both at least 2.0 and at most 1.0
}
