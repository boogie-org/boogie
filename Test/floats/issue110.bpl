// RUN: %boogie /printModel:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure Exp2(a:[int]float24e8)
{
  assert a[0] > 0x0.0e0f24e8;
}
