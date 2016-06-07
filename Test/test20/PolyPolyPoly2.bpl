// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const p: <a>[]a;
const q: <a,b>[a]b;

axiom (p[] == p[]);               // warning
axiom (p[][13 := false] == q);
axiom (p[][13 := false] == p[]);  // warning

const c: bv17;

axiom (p[] ++ p[] ++ c == p[]);   // warning
axiom (p[] ++ p[] == c);          // warning
axiom (p[] == c);

type List _;

function emptyList<a>() returns (List a);
function append<a>(List a, List a) returns (List a);

axiom (forall<a> l:List a :: append(emptyList(), l) == l);
axiom (forall<a> l:List a :: append(l, emptyList()) == l);
axiom (append(emptyList(), emptyList()) == emptyList());   // warning
axiom (forall<a> l:List a :: l==emptyList() ==> append(l, emptyList()) == emptyList());

var x: <a>[]a;
var y: <a>[a]a;

procedure P() returns () modifies x, y; {
  x[] := 15;
  x[] := false;
  x[] := p[];       // warning
  x[] := q[false];  // warning
  y[13] := q[false];
}