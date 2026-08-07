// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// A map type with no index arguments is represented by its result type, but the
// translated select kept the map type, so anything inspecting the operand type saw
// a map where it expected a value type. Arithmetic on a nullary select used to
// crash with an UnreachableException from Type.FloatSignificand (the Add/Sub/Mul
// cases assumed any operand that was neither int nor real had to be a float);
// bitvector concatenation crashed the same way in Type.BvBits; and a select
// supplying indices to a nullary map inferred the wrong result type.

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

procedure BvConcat()
{
  var x: []bv8;
  x[] := 0bv8;
  assert (x[] ++ 1bv24) == 1bv32;
}

// A select that supplies indices has to look through the nullary map wrappers to
// find the map those indices apply to.

procedure NestedNullaryMap()
{
  var x: [][int]int;
  x[][1] := 5;
  assert x[][1] + 0 == 5;
}

procedure NullaryMapOfNullaryMap()
{
  var x: [][]int;
  x[][] := 7;
  assert x[][] * 2 == 14;
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

procedure BvConcatError()
{
  var x: []bv8;
  x[] := 0bv8;
  assert (x[] ++ 1bv24) == 2bv32;  // error
}

procedure NestedNullaryMapError()
{
  var x: [][int]int;
  x[][1] := 5;
  assert x[][1] + 0 == 6;  // error
}
