// RUN: %parallel-boogie -infer:j /errorTrace:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The loops are there because inferred facts reach the prover only at loop heads.
procedure Lower(x: real, y: real)
  requires 0e0 <= x;
  requires 1e0 <= y;
{
  var p: real;
  p := x ** y;
  while (*) { }
  assert 1e0 <= p;  // 0.5 ** 1.0 is 0.5
}

procedure Upper(x: real, y: real)
  requires 0e0 <= x;
  requires 1e0 <= y;
  requires y <= 2e0;
{
  var p: real;
  p := x ** y;
  while (*) { }
  assert p <= 2e0;  // 3.0 ** 2.0 is 9.0
}
