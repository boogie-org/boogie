// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"



type C a b;
type C2 b a = C a b;


// ordering of map type parameters
function g0(<a,b>[C2 a b]int) returns (int);
function g1(<a,b>[C2 b a]int) returns (int);
function g2(<a,b>[C a b]int) returns (int);
function g3(<a,b>[C b a]int) returns (int);

const c0 : <a,b>[C2 a b]int;
const c1 : <a,b>[C2 b a]int;
const c2 : <a,b>[C a b]int;
const c3 : <a,b>[C b a]int;

axiom g0(c0) == 0;
axiom g1(c0) == 0;
axiom g2(c0) == 0;
axiom g3(c0) == 0;
axiom g0(c1) == 0;
axiom g1(c1) == 0;
axiom g2(c1) == 0;
axiom g3(c1) == 0;
axiom g0(c2) == 0;
axiom g1(c2) == 0;
axiom g2(c2) == 0;
axiom g3(c2) == 0;
axiom g0(c3) == 0;
axiom g1(c3) == 0;
axiom g2(c3) == 0;
axiom g3(c3) == 0;


type nested a = <b>[b, b, a]int;
type nested2 = nested (nested int);


function h(nested2) returns (bool);
const e : <b>[b, b, <b2>[b2, b2, int]int]int;
axiom h(e);

const e2 : <b>[b, b, <b2>[b2, b, int]int]int;      // wrong binding
axiom h(e2);

