// RUN: %parallel-boogie -infer:j /errorTrace:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Inferred invariants are injected as `assume {:inferred} ...` and never discharged, so an
// interval transfer function that reports a bound the operation can exceed is unsound: the
// assumption makes the path vacuous and false assertions verify.

// Mul: with both intervals reaching below zero, the maximum is at the two lower bounds OR at
// the two upper bounds. Taking the lower-bound product alone claimed x * y < 2 here, which
// x == y == 100 exceeds.
procedure MulBothNegativeLowerBounds(x: int, y: int)
  requires -1 <= x;
  requires -1 <= y;
{
  var r: int;
  var i: int;
  r := x * y;
  i := 0;
  while (i < 1) { i := i + 1; }
  if (x == 100 && y == 100) {
    assert false;  // error
  }
}

// Div and Mod: division by zero is uninterpreted in SMT-LIB, so with a divisor that may be
// zero the result is not bounded by anything the operands say.
procedure DivByPossiblyZero(x: int, y: int) returns (r: int)
  requires 0 <= x;
  requires 0 <= y;
  ensures 0 <= r;  // error
{
  var i: int;
  r := x div y;
  i := 0;
  while (i < 1) { i := i + 1; }
}

procedure ModByPossiblyZero(x: int, y: int) returns (r: int)
  requires 0 <= x;
  requires 0 <= y;
  ensures 0 <= r;  // error
{
  var i: int;
  r := x mod y;
  i := 0;
  while (i < 1) { i := i + 1; }
}

// RealDiv needs the same zero-divisor guard. With only y >= 0, the SMT encoding permits
// a negative value for x / 0 even when x is nonnegative.
procedure RealDivByPossiblyZero(x: real, y: real) returns (r: real)
  requires 0.0 <= x;
  requires 0.0 <= y;
  ensures 0.0 <= r;  // error
{
  var i: int;
  r := x / y;
  i := 0;
  while (i < 1) { i := i + 1; }
}

// A divisor of at least one still gives both the lower bound and r <= x.
procedure RealDivByAtLeastOne(x: real, y: real) returns (r: real)
  requires 0.0 <= x;
  requires x <= 100.0;
  requires 1.0 <= y;
  ensures 0.0 <= r;
  ensures r <= 100.0;
{
  var i: int;
  r := x / y;
  i := 0;
  while (i < 1) { i := i + 1; }
}

// The bounds are still inferred when the divisor is known to be positive.
procedure DivByPositive(x: int, y: int) returns (r: int)
  requires 0 <= x;
  requires x < 100;
  requires 1 <= y;
  ensures 0 <= r;
{
  var i: int;
  r := x div y;
  i := 0;
  while (i < 1) { i := i + 1; }
}

// And Mul keeps its bound when both intervals are bounded above.
procedure MulBothNegativeBounded(x: int, y: int) returns (r: int)
  requires -5 <= x;
  requires x <= -1;
  requires -5 <= y;
  requires y <= -1;
  ensures r <= 25;
{
  var i: int;
  r := x * y;
  i := 0;
  while (i < 1) { i := i + 1; }
}
