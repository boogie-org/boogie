// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var g0: int;
var g1: int;

var h0: [ref, name]any;
var h1: [ref, name]any;

const X: name;

procedure P(a: ref, hh: [ref, name]any) returns (b: int, hout: [ref, name]any);
  modifies a;  // in-parameters are not mutable
  modifies h1, g0;
  modifies b;  // out-parameters are not allowed explicitly in modifies clause


type ref, name, any;
