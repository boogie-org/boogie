// RUN: %boogie -noinfer -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure{:atomic}{:layer 2} atomic_P1() { }

procedure{:yields}{:layer 1} {:refines "atomic_P1"} P1();
  requires{:layer 1} false;

procedure{:yields}{:layer 2} P2()
{
  assert{:layer 1} false;
  yield;
  call P1();
  yield;
}
