// RUN: %parallel-boogie -infer:j "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// `Expr.And` and its siblings do not set `Type`, so `MeasureChecker` used to inject an untyped
// expression into a program that had already been typechecked, and `ThresholdFinder` -- which reads the
// type of what it visits -- crashed with a NullReferenceException. Only a bool measure reached it: the
// int path builds `Expr.Lt` over two identifiers, whose first operand carries a type, while the bool
// path builds `Expr.And(Expr.Not(m), m')`, whose first operand is freshly built and does not.
//
// Sixty of the corpus files crashed under -infer:j this way. The other fifty-four are Civl's, which
// builds untyped expressions of its own; those are caught by the reader rather than the producer.

var y: bool;

procedure BoolMeasure()
{
  var n: int;

  n := 10;
  while (n >= 1)
  measure n, y;
  {
    n := n - 1;
  }
}
