// RUN: %boogie -typeEncoding:n -logPrefix:0n "%s" > "%t"
// RUN: %diff "%s.n.expect" "%t"
// RUN: %boogie -typeEncoding:p -logPrefix:0p "%s" > "%t"
// RUN: %diff "%s.p.expect" "%t"
// RUN: %boogie -typeEncoding:a -logPrefix:0a "%s" > "%t"
// RUN: %diff "%s.a.expect" "%t"


const ar : [int]bool;
axiom (forall x:int :: {ar[x]} !ar[x]);

type S, T, C a b;

function m(T,S) returns (bool);
function n(T,T) returns (bool);
function f<a>(C a T, a) returns (int);
function f2<a>(C a T, a) returns (int);
function g(T) returns (T);
function h<a>(a) returns (a);
function k<a>(C a a) returns (bool);
function l<a>(a) returns (bool);
function o<a>(a) returns (bool);

const con : T;
const someConst : int;

axiom (forall <b> x:C b b :: k(x));
axiom (forall x:C S T, y : S :: f(x,y) == f2(x,y));
axiom (forall x:S, y:T :: l(x) && n(y, con) == m(y,x));
axiom (forall x:T :: {g(h(x))} {g(x)} x == x);
axiom (forall <b> x:b :: {h(x)} x == x);
axiom (forall <b> x:b, y:b :: {o(x), o(y)} o(x) ==> someConst == 42);
axiom (forall <b> x:C b b :: {k(x)} k(x));

procedure P() returns () {
  var v0 : C S S, v1 : C S T, v2 : S, v3 : T;

  assert ar[27] == false;
  assert k(v0);
  assert f(v1, v2) == f2(v1, v2);
  assert n(v3, con) == m(v3, v2);
}

procedure Q<a>(x : a) returns () {
  assert someConst == 42; // should not be provable

  assume o(x) == o(x);
  assert someConst == 42;
  assert someConst == 43; // should not be provable
}