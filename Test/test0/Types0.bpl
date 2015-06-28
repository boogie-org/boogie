// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type T, U;
type V;

function f([U,V]T, int) returns (U);
function g(x: [U,V]T, y: int) returns (z: U);
function h([U,V]T: int, y: int) returns (z: U);  // parse error
function k(T: int, y: int) returns (U: [any]int);
function l(x) returns (int);  // resolve error
