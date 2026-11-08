// RUN: %parallel-boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type C _;

const p: <a>[int]a;
const q: <a>[a, a]a;
const r: <a>[int](C a);

const x: C int;
const y: C bool;

axiom (p[0][0 := 5][0 := true] == p);
axiom (p[0][0 := 5][0 := true] == r);          // error
axiom (p[0][0 := x][0 := y] == p);
axiom (p[0][0 := x][0 := y] == r);
axiom (p[0][0 := x][0 := 5] == r);             // error
axiom (p[0][0 := x][0 := y] == p[0][0 := 5][0 := true]);
axiom (q[p[0][0 := x][0 := y], p[0][0 := 5][0 := true]] == p);
axiom (q[p[0], p[0]][0 := 5][0 := true] == p);

axiom (exists<a> x:a :: p[0][0 := 5][0 := true] == x);
axiom (exists<a,b> x:a, y:b :: p[0][0 := 5][0 := true] == q[x,y]);  // error
axiom (exists<a,b> x:a, y:b :: q[x, x] == q[y, y]);
