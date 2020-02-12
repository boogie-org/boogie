// RUN: %boogie -typeEncoding:n -logPrefix:0n "%s" > "%t"
// RUN: %diff "%s.n.expect" "%t"
// RUN: %boogie -typeEncoding:p -logPrefix:0p "%s" > "%t"
// RUN: %diff "%s.p.expect" "%t"
// RUN: %boogie -typeEncoding:a -logPrefix:0a "%s" > "%t"
// RUN: %diff "%s.a.expect" "%t"


const a, b:int;
const c:int extends a, b;

procedure P() returns () {
  var x:int;

  assert c <: a;

  assume c <: x && x <: a;
  assert x == c || a == x;

  assert x == b;             // should not be provable
}

procedure Q() returns () {
  assume b <: a;
  assert b == a;
}