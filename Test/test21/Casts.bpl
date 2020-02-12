// RUN: %boogie -typeEncoding:n -logPrefix:0n "%s" > "%t"
// RUN: %diff "%s.n.expect" "%t"
// RUN: %boogie -typeEncoding:p -logPrefix:0p "%s" > "%t"
// RUN: %diff "%s.p.expect" "%t"
// RUN: %boogie -typeEncoding:a -logPrefix:0a "%s" > "%t"
// RUN: %diff "%s.a.expect" "%t"


procedure P() returns () {
  var m : [int]int, n : [int]int, x : int;

  assume m[x] == x;
  assume n[x] == 1;

  assert n[m[x]] == 1;
  assert m[n[x]] == 1;    // should not be provable
}