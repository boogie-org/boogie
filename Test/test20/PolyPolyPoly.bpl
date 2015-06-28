// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type C _;

const p: <a>[]a;
const q: <a>[a, a]a;
const r: <a>[](C a);

const x: C int;
const y: C bool;

axiom (p[][:= 5][:= true] == p);
axiom (p[][:= 5][:= true] == r);               // error
axiom (p[][:= x][:= y] == p);
axiom (p[][:= x][:= y] == r);
axiom (p[][:= x][:= 5] == r);                  // error
axiom (p[][:= x][:= y] == p[][:= 5][:= true]);
axiom (q[p[][:= x][:= y], p[][:= 5][:= true]] == p);
axiom (q[p[], p[]][:= 5][:= true] == p);

axiom (exists<a> x:a :: p[][:= 5][:= true] == x);
axiom (exists<a,b> x:a, y:b :: p[][:= 5][:= true] == q[x,y]);  // error
axiom (exists<a,b> x:a, y:b :: q[x, x] == q[y, y]);
