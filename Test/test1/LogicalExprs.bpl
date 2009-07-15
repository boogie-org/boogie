const P: bool;
const Q: bool;

axiom (forall x: int :: x < 0);
axiom Q ==> P;
axiom (forall x: int :: x < 0) ==> P;
