// RUN: %boogie -typeEncoding:n -logPrefix:0n "%s" > "%t"
// RUN: %diff "%s.n.expect" "%t"
// RUN: %boogie -typeEncoding:p -logPrefix:0p "%s" > "%t"
// RUN: %diff "%s.p.expect" "%t"
// RUN: %boogie -typeEncoding:a -logPrefix:0a "%s" > "%t"
// RUN: %diff "%s.a.expect" "%t"
type C _;

function f<a>(C a) returns (int);

axiom (forall x : C int :: f(x) == 3);
axiom (forall x : C bool :: f(x) == 7);

procedure P() returns () {
  var a : C int, b : C bool, c : C ref;

  start:
    assert f(a) == 3;
    assert f(b) == 7;
    assert f(b) == 8;      // should not be provable
}

procedure Q() returns () {
  var c : C ref;

  start:
    assert f(c) == 7;      // should not be provable
}

procedure R<a>(c : C a) returns () {

  start:
    assert f(c) == 7;      // should not be provable
}

type ref;
