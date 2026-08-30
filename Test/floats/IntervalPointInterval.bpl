// RUN: %parallel-boogie -infer:j "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Why the domain describes no float: see IntervalNoFloatTracked.bpl, which pins that property directly.
// This file pins one consequence of it.

// A float pinned to a literal has equal bounds, and Meet tested emptiness the way it does for an int,
// where Lo == Hi means empty. So the then-branch of a float equality was inferred unreachable, and a loop
// alternating between two values reported only one of them.

procedure Alternating()
{
  var m: float24e8;
  var i: int;

  m := 0x1.0e0f24e8;
  i := 0;
  while (i < 3)
  {
    if (m == 0x1.0e0f24e8) { m := 0x2.0e0f24e8; } else { m := 0x1.0e0f24e8; }
    i := i + 1;
  }

  assert m == 0x1.0e0f24e8;  // three flips leave m at 2.0
}
