// RUN: %boogie -loopUnroll:3 -soundLoopUnrolling "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure foo(N: int)
  requires N == 2;
{
  var n, sum, recent: int;
  n, sum := 0, 0;
  while (n < N)
  {
    call recent := bar();
    sum, n := sum + recent, n + 1;
  }
  if (n == 2) {
    assert sum == recent + recent;  // no reason to believe this always to be true
  }
}

procedure {:inline 1} bar() returns (r: int)
{
  var x: int;
  r := x;
}
