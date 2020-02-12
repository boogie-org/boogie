// RUN: %boogie -typeEncoding:n -logPrefix:0n "%s" > "%t"
// RUN: %diff "%s.n.expect" "%t"
// RUN: %boogie -typeEncoding:p -logPrefix:0p "%s" > "%t"
// RUN: %diff "%s.p.expect" "%t"
// RUN: %boogie -typeEncoding:a -logPrefix:0a "%s" > "%t"
// RUN: %diff "%s.a.expect" "%t"


type Color;

const Blue, Red, Green : Color;

axiom (forall x : Color :: x == Blue || x == Red || x == Green);

procedure P() returns () {
  var x : Color;

  assume x != Blue;
  assert x == Red;        // should not be provable
}

procedure Q() returns () {
  var x : Color;

  assume x != Blue && x != Green;
  assert x == Red;
}