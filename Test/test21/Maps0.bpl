// RUN: %boogie -typeEncoding:n -logPrefix:0n "%s" > "%t"
// RUN: %diff "%s.n.expect" "%t"
// RUN: %boogie -typeEncoding:p -logPrefix:0p "%s" > "%t"
// RUN: %diff "%s.p.expect" "%t"
// RUN: %boogie -typeEncoding:a -logPrefix:0a "%s" > "%t"
// RUN: %diff "%s.a.expect" "%t"


const a : [int] bool;
const b : [int, bool] int;

function f<a>(a) returns (int);

axiom (forall x : [int] bool :: f(x) == 7);
axiom (forall y : [int, bool] int :: f(y) == 7);

procedure P() returns () {
  var x : [int] bool;

  assert f(a) > 0;
  assert f(b) > 0;

  x := a;
  x[17] := false;
  x[16] := true;

  assert x[15] == a[15] && !x[17];
  assert f(x) == 7;
  assert f(x) == 8;              // should not be provable
}


type Field a;

const heap : <a>[ref, Field a] a;

procedure Q() returns () {
  assert f(heap) > 0;      // should not be provable
}


procedure R() returns () {
  var o : ref;
  var e : Field int, g : Field bool, h : Field (Field int), i : Field int;
  var heap2 : <a>[ref, Field a] a;
  
  heap2 := heap;
  heap2[o, e] := 17;
  assert heap2 == heap[o, e := 17];

  heap2[o, g] := true;
  assert heap2[o, e] == 17 && heap2[o, g];

  heap2[o, h] := e;
  assert heap2[o, heap2[o, h]] == 17;

  heap2[o, i] := 16;
  assert heap2[o, g];
  assert heap2[o, heap2[o, h]] == 17;    // should no longer be provable
}

type ref;
