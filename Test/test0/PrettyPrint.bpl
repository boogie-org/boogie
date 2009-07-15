const x: int;
const y: int;
const z: int;
const P: bool;
const Q: bool;
const R: bool;

axiom x * (y + z) == x + (y * z);
axiom (x * y) + z == (x + y) * z;

axiom x * y * z == (x * (y * z));
axiom (x * y) * (z * x) == (x * y) * z;

axiom x / y / z == (x / (y / z));
axiom (x / y) / (z / x) == (x / y) / z;

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
