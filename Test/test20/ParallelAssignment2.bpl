// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Examples from the Boogie2 language report
// (examples where already resolution fails)

var x : int;
var y : int;
var a : [int]int;

procedure P(i:int, j:int) returns () modifies x, y, a; {
  x, y := 1;                     // wrong number of rhss
  a[i], a[j] := a[j], a[i];      // variable assigned more than once
}