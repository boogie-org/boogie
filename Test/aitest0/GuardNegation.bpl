// RUN: %parallel-boogie -infer:t -instrumentInfer:e -printInstrumented -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The desugaring of "if" and "while" negates the guard while the parser is still building blocks, before
// anything has a type, and Expr.Not will not reverse an order relation without knowing whether the type
// orders totally. Program.Typecheck asks it again afterwards, so the printed blocks below show an integer
// guard reversed and a float's left as a negation.
//
// The trivial domain is enough to get the blocks printed, and keeps whatever another domain would infer
// out of the expectation.

procedure IntGuard() returns (r: int)
{
  var i: int;
  i := 0;
  while (i < 3)
  {
    i := i + 1;
  }

  if (7 <= i)
  {
    r := 1;
  }
  else
  {
    r := 0;
  }
}

procedure FloatGuard(f: float24e8) returns (r: int)
{
  if (f < 0x1.0e0f24e8)
  {
    r := 1;
  }
  else
  {
    r := 0;
  }
}

// A bool guard has no relation to reverse either way.
procedure BoolGuard(b: bool) returns (r: int)
{
  if (b)
  {
    r := 1;
  }
  else
  {
    r := 0;
  }
}
