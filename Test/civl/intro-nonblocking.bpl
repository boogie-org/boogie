// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

link action {:layer 1} intro (x:int)
{
  assume x == 0;
}

yield procedure {:layer 1} p (x:int)
{
  call intro(x);
}
