// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


type C, D, E _;

const x:int;
const c:C;
const d:D;

axiom (x:int > 0);
axiom (x:int < 0);
axiom (x:E <a>[a]int < 0);   // impossible coercion

axiom (c:D == d);            // impossible coercion

axiom (15:D == d);           // impossible coercion
axiom (15:E int == d);       // impossible coercion
axiom ((18*15):int == 0);
