// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
const i: int;
const r: real;

axiom i == 0;
axiom i >= 0.0;                // type error
axiom i <= 0.0e0;              // type error
axiom i < 0.0e-0;              // type error
axiom i > 0.0e20;              // type error

axiom -i == r;                 // type error
axiom i + r == 0.0;            // type error
axiom i - r == 0.0;            // type error
axiom i * r == 0.0;            // type error
axiom i div r == 0;            // type error
axiom i mod r == 0;            // type error

axiom i / i == 0;              // type error
axiom i / i == 0.0;
axiom i / r == 0.0;
axiom r / i == 0.0;
axiom r / r == 0.0;

axiom i ** r == 0.0;           // type error
axiom r ** r == 0.0;

axiom real(i) == 0.0;
axiom real(i) == i;            // type error
axiom int(r) == 0;
axiom int(r) == r;             // type error
axiom int(real(i)) == i;
axiom real(int(r)) == r;
axiom int(int(r)) == i;        // type error
axiom real(real(i)) == r;      // type error

axiom i == 0;
axiom real(i) >= 0.0;
axiom real(i) <= 0.0e0;
axiom r < 0.0e-0;
axiom r > 0.0e20;

axiom -r == real(i);
axiom real(i) + r == 0.0;
axiom r - real(0) == 0.0;
axiom r * r == 0.0;
axiom r div 0 == 0;            // type error
axiom r mod 0 == 0;            // type error

axiom r ** r == 0.0;
