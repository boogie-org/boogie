// RUN: %parallel-boogie -infer:j "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// No bound holds of a NaN, as every order comparison with one is false, yet the domain bounded 0.0 / 0.0
// below by 0.

procedure NotANumber()
{
  var z: float24e8;
  var i: int;

  z := 0x0.0e0f24e8 / 0x0.0e0f24e8;
  i := 0;
  while (i < 3)
  {
    z := 0x0.0e0f24e8 / 0x0.0e0f24e8;
    i := i + 1;
  }

  assert 0x0.0e0f24e8 <= z;  // z is NaN, which is not at least 0.0
}
