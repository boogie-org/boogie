// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// A map type with no index arguments is represented by its result type, but the
// translated select kept the map type, so arithmetic on a nullary select used to
// crash with an UnreachableException from Type.FloatSignificand (the Add/Sub/Mul
// cases assumed any operand that was neither int nor real had to be a float).

procedure Add()
{
  var x: []int;
  x[] := 1;
  assert x[] + 0 == 1;
}

procedure Sub()
{
  var x: []int;
  x[] := 1;
  assert x[] - 1 == 0;
}

procedure Mul()
{
  var x: []int;
  x[] := 2;
  assert x[] * 3 == 6;
}

procedure RealDiv()
{
  var y: []real;
  y[] := 6.0;
  assert y[] / 2.0 == 3.0;
}

// The obligations above are really checked, not vacuously discharged.

procedure AddError()
{
  var x: []int;
  x[] := 1;
  assert x[] + 1 == 1;  // error
}

procedure MulError()
{
  var x: []int;
  x[] := 2;
  assert x[] * 3 == 7;  // error
}

procedure RealDivError()
{
  var y: []real;
  y[] := 6.0;
  assert y[] / 2.0 == 4.0;  // error
}
