// RUN: %boogie -typeEncoding:n -logPrefix:0n "%s" > "%t"
// RUN: %diff "%s.n.expect" "%t"
// RUN: %boogie -typeEncoding:p -logPrefix:0p "%s" > "%t"
// RUN: %diff "%s.p.expect" "%t"
// RUN: %boogie -typeEncoding:a -logPrefix:0a "%s" > "%t"
// RUN: %diff "%s.a.expect" "%t"


const b:int;
const a:int extends b complete;

const c:int extends a;
const d:int extends a;

procedure P() returns () {
  var x:int;

  assert c <: b && d <: a;

  assume x <: a && !(x <: c) && x != a;
  assert x <: d;

  assert b <: x;            // should not be provable
}