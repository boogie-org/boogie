// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type T, U;
type V;

function h(T) returns (int);
function k(x:T) returns (int);
function l(x) returns (int);  // resolve error
function m(x, x) returns (bool);  // resolve error
