// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Every float comparison is false at NaN, so a NaN reaches each else branch and loop exit below, and none
// of the assertions holds of it.

procedure Lt(x: float24e8)
{
  if (x < 0x1.0e0f24e8) { } else { assert 0x1.0e0f24e8 <= x; }
}

// "x <= x" is false exactly at NaN.
procedure Le(x: float24e8)
{
  if (x <= x) { } else { assert false; }
}

procedure Gt(x: float24e8)
{
  if (x > 0x1.0e0f24e8) { } else { assert x <= 0x1.0e0f24e8; }
}

procedure Ge(x: float24e8)
{
  if (x >= 0x1.0e0f24e8) { } else { assert x < 0x1.0e0f24e8; }
}

procedure LoopExit(x: float24e8)
{
  while (x < 0x1.0e0f24e8) { }
  assert 0x1.0e0f24e8 <= x;
}
