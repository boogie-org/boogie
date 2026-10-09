// RUN: ! %boogie /trackVerificationCoverage "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The coverage label of the assumption with id a, aux$$assume$$a, is a fixed name too.

function {:builtin "aux$$assume$$a"} b(): bool;

procedure P()
{
  assume {:id "a"} true;
  assume !b();
  assert false;
}
