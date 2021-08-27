// RUN: %parallel-boogie -typeEncoding:p -logPrefix:0p "%s" > "%t"
// RUN: %diff "%s.p.expect" "%t"
// RUN: %parallel-boogie -typeEncoding:a -logPrefix:0a "%s" > "%t"
// RUN: %diff "%s.a.expect" "%t"

procedure P() returns () {
var a : <t>[t]int;

a[5] := 0;
a[true] := 1;
assert a[5] == 0;
}
