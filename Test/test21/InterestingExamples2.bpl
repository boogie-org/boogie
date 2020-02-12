// RUN: %boogie -typeEncoding:n -logPrefix:0n "%s" > "%t"
// RUN: %diff "%s.n.expect" "%t"
// RUN: %boogie -typeEncoding:p -logPrefix:0p "%s" > "%t"
// RUN: %diff "%s.p.expect" "%t"
// RUN: %boogie -typeEncoding:a -logPrefix:0a "%s" > "%t"
// RUN: %diff "%s.a.expect" "%t"


procedure P() returns () {
var m : <a>[a]ref;
var n : <b>[b]b;
var o : ref;

m[5] := null;
assert m[true := o][5] == null;
assert m[n[true] := o][5] == null;
}

type ref;
const null : ref;
