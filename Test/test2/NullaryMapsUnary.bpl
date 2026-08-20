// RUN: %boogie /proverOpt:LOGIC=AUFLIA "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// A map type with no index arguments is represented by its result type, but the
// translated select keeps the map type. Unary minus tested the operand type without
// looking through the nullary map, so an integer negation was neither int nor real
// as far as the test could tell and fell through to the real case, emitting real
// subtraction over an integer term. The logic is pinned to AUFLIA because a logic
// that has reals accepts the mistyped term silently; without reals the prover
// rejects the query outright.

procedure Neg()
{
  var x: []int;
  x[] := 1;
  assert -x[] == -1;
}

procedure NegNullaryMapOfNullaryMap()
{
  var x: [][]int;
  x[][] := 1;
  assert -x[][] == -1;
}

procedure NegUnderIfThenElse()
{
  var x: []int;
  x[] := 1;
  assert -(if true then x[] else 0) == -1;
}

procedure NegUnderQuantifier()
{
  var x: []int;
  x[] := 1;
  assert (forall i: int :: -x[] + i < i);
}

// The other unary opcode does not inspect the operand type, so it was unaffected.

procedure Not()
{
  var b: []bool;
  b[] := true;
  assert (!b[]) == false;
}

// The obligations above are really checked, not vacuously discharged.

procedure NegError()
{
  var x: []int;
  x[] := 1;
  assert -x[] == 1;  // error
}

procedure NotError()
{
  var b: []bool;
  b[] := true;
  assert (!b[]) == true;  // error
}
