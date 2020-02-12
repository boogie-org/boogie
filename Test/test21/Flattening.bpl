// RUN: %boogie -typeEncoding:n -logPrefix:0n "%s" > "%t"
// RUN: %diff "%s.n.expect" "%t"
// RUN: %boogie -typeEncoding:p -logPrefix:0p "%s" > "%t"
// RUN: %diff "%s.p.expect" "%t"
// RUN: %boogie -typeEncoding:a -logPrefix:0a "%s" > "%t"
// RUN: %diff "%s.a.expect" "%t"


function g(int) returns (int);
function f(bool) returns (int);


axiom (f((exists x:int :: g(x) >= 12)) == 3);
axiom (f((exists x:int :: g(f((forall y:int :: g(x+y) >= 0))) >= 12)) == 3);


procedure P() returns () {
  assert false;
}