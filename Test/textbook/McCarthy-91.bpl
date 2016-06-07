// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// McCarthy 91 function
procedure F(n: int) returns (r: int)
  ensures 100 < n ==> r == n - 10;
  ensures n <= 100 ==> r == 91;
{
  if (100 < n) {
    r := n - 10;
  } else {
    call r := F(n + 11);
    call r := F(r);
  }
}
