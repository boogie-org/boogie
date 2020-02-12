// RUN: %boogie -typeEncoding:n -logPrefix:0n "%s" > "%t"
// RUN: %diff "%s.n.expect" "%t"
// RUN: %boogie -typeEncoding:p -logPrefix:0p "%s" > "%t"
// RUN: %diff "%s.p.expect" "%t"
// RUN: %boogie -typeEncoding:a -logPrefix:0a "%s" > "%t"
// RUN: %diff "%s.a.expect" "%t"
type C _;

function f<a>(C a) returns (int);

axiom (forall<a> x : C a :: f(x) == 42);

procedure P(a : C int) returns () {

  start:
    assert f(a) == 42;
    assert f(a) == 43;       // should not be provable
}

procedure Q<a>(c : C a) returns () {

  start:
    assert f(c) == 42;
    assert f(c) == 43;       // should not be provable
}

function g<a,b>(a, b) returns (int);


axiom (forall x : int, y : bool :: g(x,y) == 13);
axiom (forall<a> x : int, y : C a :: g(x,y) == 42);
axiom (forall<a,z> x : C z, y : C a :: g(x,y) == 43);

procedure R() returns () {

  start:
    assert g(7, true) == 13;
    assert g(7, false) == 15;       // should not be provable
}

procedure S<b>(y : C b) returns () {

  start:
    assert g(3, y) == f(y);
    assert g(y, false) == 15;       // should not be provable
}

procedure T<a,b>(y : C b, param : a) returns () {
  var x : C a; var z : C b;

  start:
    assert g(y, x) == g(x, y);
    assert g(y, x) == 43;
    assert g(f(x), y) == 42;
    assert g(y, z) == 15;       // should not be provable
}


type D _ _;

procedure U() returns () {
    var u : D int bool, v : D bool int;

  start:
    assume (forall<a,b> x:D a b, y:b :: g(x, y) == -3);

    assert g(v, 32) == -3;
    assert g(v, 716371398712982312321) == -3;
    assert g(u, 1) == -3;       // should not be provable
}
