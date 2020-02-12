// RUN: %boogie -typeEncoding:n -logPrefix:0n "%s" > "%t"
// RUN: %diff "%s.n.expect" "%t"
// RUN: %boogie -typeEncoding:p -logPrefix:0p "%s" > "%t"
// RUN: %diff "%s.p.expect" "%t"
// RUN: %boogie -typeEncoding:a -logPrefix:0a "%s" > "%t"
// RUN: %diff "%s.a.expect" "%t"



function f<a>(a) returns (bool);
function g(int) returns (bool);

axiom (forall x:int :: f(x));
axiom (forall x:int :: g(x));

procedure P() returns () {
  var x : int, m : [int]int;
  assert f(x);
  assert f(m[x]);
  assert g(x);
  assert g(m[x]);
  assert f(true);   // should not be provable
}