// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Let's test some Boogie 2 features ...

type elements;

type Field a;
var heap : <a> [ref, Field a] a;

const emptyset : <a> [a] bool;

function union(<a> [a] bool, <a> [a] bool) returns (<a> [a] bool);

axiom (forall x : <a> [a] bool, y : <a> [a] bool,
              z : int ::         
              { union(x, y)[z] } 
              union(x, y)[z] == (x[z] || y[z]));

var tau : <a> [ref] int;             // error: type variable has to occur in arguments

axiom (forall x : int :: !emptyset[x]);

// the more general version of the axiom that also uses type quantifiers

axiom (forall<alpha>
              x : <a> [a] bool, y : <a> [a] bool,
              z : alpha ::         
              { union(x, y)[z] } 
              union(x, y)[z] == (x[z] || y[z]));

axiom (forall<beta, alpha, beta> a:alpha, b:beta ::        // error: variable bound twice
              a == b ==> (exists c:alpha :: c == b));

axiom (forall<beta> a:alpha, b:beta ::                     // error: alpha is not declared
              a == b ==> (exists c:alpha :: c == b));

type ref;
