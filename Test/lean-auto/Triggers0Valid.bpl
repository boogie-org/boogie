// RUN: %parallel-boogie -typeEncoding:p -logPrefix:0p "%s" > "%t"
// RUN: %parallel-boogie -typeEncoding:a -logPrefix:0a "%s" > "%t"

const ar : [int]bool;
axiom {:include_dep} (forall x:int :: {ar[x]} !ar[x]);

type S, T, C a b;

function m(T,S) returns (bool);
function n(T,T) returns (bool) uses {
  axiom (forall x:S, y:T :: l(x) && n(y, con) == m(y,x));
}

function f<a>(C a T, a) returns (int);
function f2<a>(C a T, a) returns (int) uses {
  axiom (forall x:C S T, y : S :: f(x,y) == f2(x,y));
}

function g(T) returns (T) uses {
  axiom (forall x:T :: {g(h(x))} {g(x)} x == x);
}

function h<a>(a) returns (a) uses {
  axiom (forall <b> x:b :: {h(x)} x == x);
}

function k<a>(C a a) returns (bool) uses {
  axiom (forall <b> x:C b b :: k(x));
  axiom (forall <b> x:C b b :: {k(x)} k(x));
}

function l<a>(a) returns (bool);
function o<a>(a) returns (bool) uses {
  axiom (forall <b> x:b, y:b :: {o(x), o(y)} o(x) ==> someConst == 42);
}

const con : T;
const someConst : int;

procedure P() returns () {
  var v0 : C S S, v1 : C S T, v2 : S, v3 : T;

  assert ar[27] == false;
  assert k(v0);
  assert f(v1, v2) == f2(v1, v2);
  assert n(v3, con) == m(v3, v2);
}
