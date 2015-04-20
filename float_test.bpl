procedure F(n: int) returns (r: int)
  ensures 100 < n ==> r == n - 10;  // This postcondition is easy to check by hand
  ensures n <= 100 ==> r == 91;     // Do you believe this one is true?
{
  if (100 < n) {
    r := n - 10;
  } else {
    call r := F(n + 11);
    call r := F(r);
  }
}