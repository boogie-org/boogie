// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Negating an order relation gives the reverse relation only where the order is total. Every IEEE
// comparison is false when an operand is NaN, so the else branch of a float comparison is reached by a
// NaN and must not be told the reverse relation holds. Equality is unaffected: Boogie's == on floats is
// bit identity, so != really is its complement.

// The else branch admits a NaN, of which no bound holds.
procedure ElseBranch(x: float24e8)
{
  if (x < 0x1.0e0f24e8) { } else { assert 0x1.0e0f24e8 <= x; }  // x can be NaN
}

// "x <= x" is how the language says "x is not NaN", so its negation is satisfiable.
procedure BothBranchesLive(x: float24e8)
{
  if (x <= x) { } else { assert false; }  // reached by a NaN
}

// The loss escapes the branch: after the join, nothing new is known about x.
procedure PastTheJoin(x: float24e8)
{
  if (x < 0x1.0e0f24e8) { } else { }
  assert x <= x;  // x can still be NaN
}

// A loop guard is negated on the exit edge, with the same consequence.
procedure LoopExit(x: float24e8)
{
  while (x < 0x1.0e0f24e8) { }
  assert x <= x;  // x can still be NaN
}

// Equality is total, so complementing it stays correct and this must verify.
procedure EqualityIsTotal(x: float24e8, y: float24e8)
{
  if (x == y) { } else { assert x != y; }
}

// Integers and reals are totally ordered, so their branches lose nothing.
procedure IntegersUnaffected(i: int)
{
  if (i < 3) { } else { assert 3 <= i; }
}

procedure RealsUnaffected(r: real)
{
  if (r < 3e0) { } else { assert 3e0 <= r; }
}
