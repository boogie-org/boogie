// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type C a _ b;
type D;
type E _;

var A0 : D;

var A1 : C D D D;

var A2 : <a,b> [b, C a b D] C a D [D]a;

var A3 : <a,b> [b, C a int D] C bool ref [bv32]a;

var A4 : <a,a> [a] a;            // error: a bound twice
var A5 : <a> [a] <a> [a] int;    // error: a bound twice

var A6 : <a> [a] <b> [b] int;

var A7 : <a> [a] <b> [int] int;  // error: b does not occur as map argument

type C _ _;                      // error: C is already declared

var A8 : C int ref;              // error: wrong number of arguments

var A9 : A0;                     // error: undeclared type
var A10: F int;                  // error: undeclared type

var A11: E D;
var A12: E E D;                  // error: wrong number of arguments
var A13: E (E D);
var A14: E E E D;                // error: wrong number of arguments

var A15: E E int;                // error: wrong number of arguments
var A16: E (E int);

var A17: bv64;
var A18: [int] bv64;

var A19: C E E D;                // error: wrong number of arguments
var A20: C (E (E D)) int [int] int;
var A21: C (<a> [a] <b> [b] int) int [int] int;

var A22: (D);
var A23: ((D));

type ref;
