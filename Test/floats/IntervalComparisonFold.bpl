// RUN: %parallel-boogie -infer:j "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Comparing two float literals' bounds under the half-open reading decided the comparison the wrong way.

procedure LiteralComparison()
{
  var b: bool;
  var i: int;

  b := 0x1.8e0f24e8 <= 0x1.4e0f24e8;
  i := 0;
  while (i < 3)
  {
    b := 0x1.8e0f24e8 <= 0x1.4e0f24e8;
    i := i + 1;
  }

  assert b;  // 1.5 <= 1.25 is false
}
