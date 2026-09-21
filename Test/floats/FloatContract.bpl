// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The contract documented on FloatType, for the parts of it no other test pins. Equal2.bpl already
// covers that "==" separates the two zeros and that fp.eq ties them; SpecialValues.bpl covers fp.eq at
// NaN. What is left is that "==" is total where the order relations are not, which is the asymmetry every
// transform over float expressions has to respect.

// "==" is SMT "=": total, and so reflexive even at NaN.
procedure EqualityIsTotal(x: float24e8)
{
  assert x == x;
}

// The order relations are fp.leq and friends: false whenever an operand is NaN. So "x <= x" is not a
// tautology, and this is the one procedure here that must fail.
procedure OrderIsPartial(x: float24e8)
{
  assert x <= x;
}

// It holds exactly off NaN, which is how the core language says "x is not a NaN".
procedure OrderIsReflexiveOffNaN(x: float24e8)
{
  if (!(x == 0NaN24e8)) { assert x <= x; }
}

// The order ties the zeros where "==" separates them.
procedure OrderTiesTheZeros()
{
  assert 0x0.0e0f24e8 <= -0x0.0e0f24e8 && -0x0.0e0f24e8 <= 0x0.0e0f24e8;
  assert !(0x0.0e0f24e8 == -0x0.0e0f24e8);
}

// Arithmetic gives a NaN for 0/0, which no bound relates to.
procedure ArithmeticMakesNaN()
{
  assert (0x0.0e0f24e8 / 0x0.0e0f24e8) == 0NaN24e8;
}
