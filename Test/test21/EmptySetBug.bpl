// RUN: %boogie -typeEncoding:n -logPrefix:0n "%s" > "%t"
// RUN: %diff "%s.n.expect" "%t"
// RUN: %boogie -typeEncoding:p -logPrefix:0p "%s" > "%t"
// RUN: %diff "%s.p.expect" "%t"
// RUN: %boogie -typeEncoding:a -logPrefix:0a "%s" > "%t"
// RUN: %diff "%s.a.expect" "%t"
type ref;

const null: ref;

type Set T = [T]bool;

function Set#Empty<T>() returns (Set T);

axiom (forall<T> o: T :: { Set#Empty()[o] } !Set#Empty()[o]);

function Set#Singleton<T>(T) returns (Set T);

axiom (forall<T> r: T :: { Set#Singleton(r) } Set#Singleton(r)[r]);

axiom (forall<T> r: T, o: T :: { Set#Singleton(r)[o] } Set#Singleton(r)[o] <==> r == o);

function Set#UnionOne<T>(Set T, T) returns (Set T);

axiom (forall<T> a: Set T, x: T, o: T :: { Set#UnionOne(a, x)[o] } Set#UnionOne(a, x)[o] <==> o == x || a[o]);

procedure Test(this: ref)
{
  var s: Set ref;

  s := Set#UnionOne(Set#Empty(), this);
  assert s[this];
  assert !Set#Empty()[this];

  assert Set#Singleton(this)[null];         // should not be provable
}
