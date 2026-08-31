// RUN: %parallel-boogie -infer:j "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The only source of "3 <= i" is the first loop's exit edge, and i is reassigned in a second loop,
// so the fact has to survive as an inferred invariant at the second loop head.
procedure P()
{
  var i: int;
  var k: int;
  i := 0;
  while (i < 3) { i := i + 1; }
  k := 0;
  while (k < 2) { i := i + 1; k := k + 1; }
  assert 3 <= i;
}
