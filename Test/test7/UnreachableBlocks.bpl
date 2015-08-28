// RUN: %boogie -vc:nested "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// In the following program, block "A" has no dominator, which would cause Boogie
// to crash if Boogie didn't first remove unreachable blocks.  That is essentially
// what this test tests
procedure P()
{
entry:
  goto A;
A:
  return;
B:
  goto A;
}

procedure Q()
{
entry:
  goto entry, A;
A:
  return;
}

procedure R()
{
entry:
  return;
A:
  goto A;
}

procedure S()
{
entry:
  return;
A:
  goto C;
B:
  goto C;
C:  // C has no dominator
  return;
}
