// RUN: %parallel-boogie -infer:j "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Why the domain describes no float: see IntervalNoFloatTracked.bpl. The other Interval*.bpl files pin
// consequences of that; this one pins the other half, that everything else still works.

// The other half of the change: variables the domain can describe are still tracked in a program that
// mentions floats. The assertion below does not follow from the loop's exit condition, only from an
// inferred invariant about j.

procedure IntervalsStillInferred()
{
  var z: float24e8;
  var i: int;
  var j: int;

  i := 0;
  j := 0;
  while (i < 3)
  {
    z := 0x1.0e0f24e8;
    i := i + 1;
    j := j + 1;
  }

  assert 0 <= j;
}
