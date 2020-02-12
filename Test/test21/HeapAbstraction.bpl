// RUN: %boogie -typeEncoding:n -logPrefix:0n "%s" > "%t"
// RUN: %diff "%s.n.expect" "%t"
// RUN: %boogie -typeEncoding:p -logPrefix:0p "%s" > "%t"
// RUN: %diff "%s.p.expect" "%t"
// RUN: %boogie -typeEncoding:a -logPrefix:0a "%s" > "%t"
// RUN: %diff "%s.a.expect" "%t"


type Field a, Heap = <a>[ref, Field a]a;

function f<b>(<a>[b, Field a]a) returns (int);

axiom (forall x:<a>[int, Field a]a :: f(x) == 17);

axiom (forall x:<a>[ref, Field a]a :: f(x) == 42);

procedure P() returns () {
  var h : Heap, g : <a>[bool, Field a]a;

  assert f(h) == 42;
  assert f(g) >= 0;     // should not be provable
}

type ref;
const null : ref;
