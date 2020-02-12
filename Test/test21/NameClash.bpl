// RUN: %boogie -typeEncoding:n -logPrefix:0n "%s" > "%t"
// RUN: %diff "%s.n.expect" "%t"
// RUN: %boogie -typeEncoding:p -logPrefix:0p "%s" > "%t"
// RUN: %diff "%s.p.expect" "%t"
// RUN: %boogie -typeEncoding:a -logPrefix:0a "%s" > "%t"
// RUN: %diff "%s.a.expect" "%t"


function f(int) returns (int);
axiom f(13) == 0;

procedure P() returns () {
  assert (exists f:int :: 0 == f(f));
}