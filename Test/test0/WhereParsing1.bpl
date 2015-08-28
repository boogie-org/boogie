// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
const x: int;

function R(int) returns (bool);
function Even(int) returns (bool);

var y: int where R(y);
var g: int where g == 12;

procedure P(x: int where x > 0) returns (y: int where y < 0);
  requires x < 100;
  modifies g;
  ensures -100 < y;

function f(a: int, b: int where b < 0)  // error: where not allowed among function parameters
    returns (bool);
