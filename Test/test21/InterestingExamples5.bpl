// RUN: %boogie -typeEncoding:n -logPrefix:0n "%s" > "%t"
// RUN: %diff "%s.n.expect" "%t"
// RUN: %boogie -typeEncoding:p -logPrefix:0p "%s" > "%t"
// RUN: %diff "%s.p.expect" "%t"
// RUN: %boogie -typeEncoding:a -logPrefix:0a "%s" > "%t"
// RUN: %diff "%s.a.expect" "%t"


type C a;

function f<a>(C a) returns (int);

//axiom (forall<a> x:C a :: {f(x)} (exists y:C a :: f(y) == 42));

function g<a>(C a) returns (C a);
axiom (forall<a> x:C a :: f(g(x)) == 42);

procedure P() returns () {
  var z : C int;
  assume g(z) == z;
  assert (exists x : C int :: f(x) == 42);
}