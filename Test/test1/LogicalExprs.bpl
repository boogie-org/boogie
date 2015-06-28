// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
const P: bool;
const Q: bool;

axiom (forall x: int :: x < 0);
axiom Q ==> P;
axiom (forall x: int :: x < 0) ==> P;
