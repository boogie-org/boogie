// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

yield procedure {:layer 94} Test()
{
  assert{:layer 94} 2 + 2 == 3;
}
