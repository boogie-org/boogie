// RUN: %parallel-boogie -infer:j "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The literal 1.5 has bounds [1, 2), and read half-open, as an int's, those denote just 1, so z != 1.5
// raised z's lower bound from 1 to 2.

procedure Disequality()
{
  var z: float24e8;
  var i: int;

  havoc z;
  assume 0x1.0e0f24e8 <= z;
  if (z != 0x1.8e0f24e8)
  {
    i := 0;
    while (i < 3) { i := i + 1; }
    assert 0x2.0e0f24e8 <= z;  // z can be 1.25
  }
}
