// RUN: %parallel-boogie -infer:j "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Why the domain describes no float: see IntervalNoFloatTracked.bpl, which pins that property directly.
// This file pins one consequence of it.

// NaN has no value for a bound to relate to, and every comparison against it is false, so a bound reached
// through arithmetic that produces NaN is an inconsistent invariant.

procedure NotANumber()
{
  var z: float24e8;
  var i: int;

  z := 0x0.0e0f24e8 / 0x0.0e0f24e8;
  i := 0;
  while (i < 3)
  {
    z := 0x0.0e0f24e8 / 0x0.0e0f24e8;
    i := i + 1;
  }

  assert 0x0.0e0f24e8 <= z;  // z is NaN, which is not at least 0.0
}
