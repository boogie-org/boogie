// RUN: %boogie -typeEncoding:n -logPrefix:0n "%s" > "%t"
// RUN: %diff "%s.n.expect" "%t"
// RUN: %boogie -typeEncoding:p -logPrefix:0p "%s" > "%t"
// RUN: %diff "%s.p.expect" "%t"
// RUN: %boogie -typeEncoding:a -logPrefix:0a "%s" > "%t"
// RUN: %diff "%s.a.expect" "%t"


axiom (forall x:bool :: x || !x);
axiom (forall x:bool :: x == true || x == false);

procedure P() returns () {
  var i : int;
  var j : bool;

  assert i != 3 || i != 4;
  assert j || !j;

  assert false;
}