// RUN: %parallel-boogie -infer:j "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The interval domain (-infer:j) emitted a bound on a float as a literal of that float's own format, and
// BigFloat.FromBigInt throws rather than rounds when the integer does not fit the format exactly. Bounds
// it computed by adding two literals need not fit, so this used to end in an unhandled ArgumentException
// during inference. The domain no longer bounds a float at all.

procedure Sum()
{
  var z: float24e8;
  var i: int;

  z := 0xF.FFFFFe5f24e8 + 0x1.0e6f24e8;  // 16777215.0 + 16777216.0, whose floors sum to 2^25 - 1
  i := 0;
  while (i < 3)
  {
    z := 0xF.FFFFFe5f24e8 + 0x1.0e6f24e8;
    i := i + 1;
  }
}
