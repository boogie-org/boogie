const i: int;
const r: real;

axiom i == 0;
axiom i >= 0.0;				// type errror
axiom i <= 0.0e0;			// type errror
axiom i < 0.0e-0;			// type errror
axiom i > 0.0e20;			// type errror

axiom -i == r;				// type errror
axiom i + r == 0.0;			// type errror
axiom i - r == 0.0;			// type errror
axiom i * r == 0.0;			// type errror
axiom i div r == 0;			// type errror
axiom i mod r == 0;			// type errror

axiom i / i == 0;			// type errror
axiom i / i == 0.0;
axiom i / r == 0.0;
axiom r / i == 0.0;
axiom r / r == 0.0;

axiom i ** r == 0.0;		// type errror
axiom r ** r == 0.0;

axiom real(i) == 0.0;
axiom real(i) == i;			// type errror
axiom int(r) == 0;
axiom int(r) == r;			// type errror
axiom int(real(i)) == i;
axiom real(int(r)) == r;
axiom int(int(r)) == i;		// type errror
axiom real(real(i)) == r;	// type errror

axiom i == 0;
axiom real(i) >= 0.0;
axiom real(i) <= 0.0e0;
axiom r < 0.0e-0;
axiom r > 0.0e20;

axiom -r == real(i);
axiom real(i) + r == 0.0;
axiom r - real(0) == 0.0;
axiom r * r == 0.0;
axiom r div 0 == 0;			// type errror
axiom r mod 0 == 0;			// type errror

axiom r ** r == 0.0;
