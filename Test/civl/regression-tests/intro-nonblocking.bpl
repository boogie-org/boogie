// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

pure action intro (x:int)
{
  assume x == 0;
}
