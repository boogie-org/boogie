// RUN: %parallel-boogie -infer:j -instrumentInfer:e -printInstrumented -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Pow is encoded as an uninterpreted function without axioms. Bounds on its operands
// therefore imply no bound on its result.
procedure PowNonnegativeOperands(x: real, y: real)
  requires 0.0 <= x;
  requires 0.0 <= y;
{
  var r: real;
  var i: int;
  r := x ** y;
  i := 0;
  while (i < 1) { i := i + 1; }
}

// Even a base of at least one does not imply a bound without axioms for Pow.
procedure PowBaseAtLeastOne(x: real, y: real)
  requires 1.0 <= x;
  requires 0.0 <= y;
{
  var r: real;
  var i: int;
  r := x ** y;
  i := 0;
  while (i < 1) { i := i + 1; }
}
