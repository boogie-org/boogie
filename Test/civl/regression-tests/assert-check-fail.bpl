// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

yield procedure {:layer 4} Main()
ensures {:layer 3} false;
{
  assert {:layer 1} false;
  call Helper();
}

yield procedure {:layer 4} Helper()
requires {:layer 2} false;
{ }