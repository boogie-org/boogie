// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
action {:layer 2} atomic_P1() { }

yield procedure {:layer 1} P1() refines atomic_P1
requires{:layer 1} false;
{ }

yield procedure {:layer 2} P2()
{
  assert{:layer 1} false;
  call P1();
}
