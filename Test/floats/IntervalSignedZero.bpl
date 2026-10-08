// RUN: %parallel-boogie -infer:j "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// A one-point interval was emitted as an equality, which is wrong for a float: -0.0 and +0.0 share the
// value 0, but Boogie's == keeps them apart.

procedure SignedZero()
{
  var z: float24e8;
  var i: int;

  z := -0x0.0e0f24e8;
  i := 0;
  while (i < 3)
  {
    z := -0x0.0e0f24e8;
    i := i + 1;
  }

  assert z == 0x0.0e0f24e8;  // z is -0.0, which is not +0.0
}
