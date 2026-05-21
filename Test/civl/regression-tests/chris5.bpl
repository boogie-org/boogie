// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 1,1} g:int;

pure action P(x:int)
{
  assert x == 0;
}

yield procedure {:layer 1} Y(x:int)
{
  call {:layer 1} P(x);
  assert {:layer 1} x == 0;
}
