// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function f(int) returns (bool);
axiom (forall int x :: f(x) <== x >= 0);
