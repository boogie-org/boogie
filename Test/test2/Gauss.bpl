// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure sum(n: int) returns (s: int)
requires n >= 0;
ensures s == (n * (n + 1)) div 2;
{
  var i: int;

  i := 0;
  s := 0;
  while (i < n)
  invariant 0 <= i && i <= n;
  invariant s == (i * (i + 1)) div 2;
  {
    i := i + 1;
    s := s + i;
  }
}
