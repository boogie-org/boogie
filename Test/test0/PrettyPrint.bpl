// RUN: %boogie -pretty:0 -noVerify -printInstrumented "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
const x: int;
const y: int;
const z: int;
const r: real;
const s: real;
const t: real;
const P: bool;
const Q: bool;
const R: bool;

axiom x * (y + z) == x + (y * z);
axiom (x * y) + z == (x + y) * z;

axiom x * y * z == (x * (y * z));
axiom (x * y) * (z * x) == (x * y) * z;

axiom x div y div z == (x div (y div z));
axiom (x div y) div (z div x) == (x div y) div z;

axiom x + y mod z == ((y mod z) + x);
axiom (x + y) mod z == (x mod z) + (y mod z);

axiom x / y / z == (x / (y / z));
axiom (x / y) / (z / x) == (x / y) / z;
axiom x / s / z == (x / (s / z));
axiom (x / s) / (z / x) == (x / s) / z;
axiom r / s / t == (r / (s / t));
axiom (r / s) / (t / r) == (r / s) / t;

axiom ((r * s) / t) == r * s / t;
axiom ((r / s) * t) == (r / s) * t;

axiom (r * s) ** t == (r ** t) * (s ** t);
axiom r ** (s + t) == r ** s * r ** t;

axiom int(real(x)) == x;
axiom r >= 0.0 ==> real(int(r)) <= r;
axiom int(0e-3 - 0.02) == 0;
axiom int(0e2 - 3.5e1) == -35;
axiom int(27e-1) == 2;

axiom x - y - z == (x - (y - z));
axiom (x - y) - (z - x) == (x - y) - z;

axiom x + y - z - x + y == 0;
axiom ((((x + y) - z) - x) + y) == (x + (y - (z - (x + y))));

axiom P ==> Q ==> R <==> (P ==> (Q ==> R));
axiom ((P ==> Q) ==> (R ==> P)) == ((P ==> Q) ==> R);

axiom P <==> Q <==> R;
axiom P ==> Q <==> Q ==> R <==> R ==> P;

axiom (P && Q) || (Q && R);
axiom (P || Q) && (Q || R);
axiom (P || Q) || (Q || R);
axiom (P && Q) && (Q && R);

// -------------- quantifier key-value decorations

function f(int) returns (int);

axiom (forall x: int :: {:xname "hello"}
              {  :weight 5} {f(x+x)}   {:ValueFunc f(x+1)  }  {f(x)*f(x)} {:nopats f(x+x+x)}
         f(f(x)) < 200);
