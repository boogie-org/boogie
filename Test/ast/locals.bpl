// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure MonotonicIsNotHavoced()
{
  var x: int;
  monotonic var assigned: bool;
  x := 5;
  assigned := true;
  while (x > 0)
  {
    x := x - 1;
    assigned := true;
  }
  assert assigned;
}