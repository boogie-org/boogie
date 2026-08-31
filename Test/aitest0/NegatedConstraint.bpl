// RUN: %parallel-boogie -infer:j -instrumentInfer:e -printInstrumented -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// A negation written by hand never went through Expr.Not, so the domain ignored it. It now pushes the
// negation inwards with the same rewriting Expr.Not applies elsewhere, which by then has the types it
// needs. Three shapes it did not read before, and one it must still refuse.

procedure NegatedComparisons()
{
  var i: int;
  var j: int;

  havoc i, j;
  assume !(i < 3);         // i >= 3
  assume !(7 <= j);        // j < 7
}

procedure NegatedEquality()
{
  var x: int;

  havoc x;
  assume 5 <= x;
  assume !(x == 5);        // with the bound above, x >= 6
}

procedure DoubleNegation()
{
  var y: int;

  havoc y;
  assume !!(3 <= y);       // y >= 3
}

// A float's order is partial, so a negated float comparison holds of a NaN and the reverse relation does
// not. Expr.Not declines to reverse it and hands the negation back unchanged, which is how the domain
// recognises there is nothing to learn: no element below mentions f.
procedure FloatRefused(f: float24e8)
{
  var k: int;

  k := 0;
  assume !(f < 0x1.0e0f24e8);
}
