// RUN: %parallel-boogie -typeEncoding:p -logPrefix:0p "%s" > "%t"
// RUN: %diff "%s.p.expect" "%t"
// RUN: %parallel-boogie -typeEncoding:a -logPrefix:0a "%s" > "%t"
// RUN: %diff "%s.a.expect" "%t"

type T;

function f() returns (int);      // functions without arguments
function g() returns (T);


const c : T;

axiom (f() >= 13);
axiom (g() != c);

procedure P() returns () {
  var x : int;

  x := f();

  assert x >= 0 && f() >= 7;
  assert g() != c;
  assert f() >= 20;            // should not be provable
}
