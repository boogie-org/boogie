// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Test old appearing in illegal locations

var Global0: int;

// Bad
procedure OldInCode1()
  requires old(Global0) == 0;
{
  start:
    return;
}

// Bad
axiom (forall o:ref :: old(o) == o);

type ref;
