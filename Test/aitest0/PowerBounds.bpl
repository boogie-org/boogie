// RUN: %parallel-boogie -infer:j -printInstrumented -noVerify "%s" > "%t"
// RUN: %OutputCheck "--file-to-check=%t" "%s"
// CHECK-NOT-L: 1e0 <= p
// CHECK-NOT-L: p <= 2e0

// Neither bound holds: 0.5 ** 1.0 is 0.5, and 3.0 ** 2.0 is 9.0.
procedure Pow(x: real, y: real)
  requires 0e0 <= x;
  requires 1e0 <= y;
  requires y <= 2e0;
{
  var p: real;
  p := x ** y;
  while (*) { }
}
