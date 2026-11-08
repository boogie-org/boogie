// RUN: %parallel-boogie -typeEncoding:p -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const p: <a>[int]a;
const q: <a,b>[a]b;

axiom (p[0] == p[0]);               // warning
axiom (p[0][13 := false] == q);
axiom (p[0][13 := false] == p[0]);  // warning

const c: bv17;

axiom (p[0] ++ p[0] ++ c == p[0]);  // warning
axiom (p[0] ++ p[0] == c);          // warning
axiom (p[0] == c);

type List _;

function emptyList<a>() returns (List a);
function append<a>(List a, List a) returns (List a);

axiom (forall<a> l:List a :: append(emptyList(), l) == l);
axiom (forall<a> l:List a :: append(l, emptyList()) == l);
axiom (append(emptyList(), emptyList()) == emptyList());   // warning
axiom (forall<a> l:List a :: l==emptyList() ==> append(l, emptyList()) == emptyList());

var x: <a>[int]a;
var y: <a>[a]a;

procedure P() returns () modifies x, y; {
  x[0] := 15;
  x[0] := false;
  x[0] := p[0];      // warning
  x[0] := q[false];  // warning
  y[13] := q[false];
}
