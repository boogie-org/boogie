// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Examples from the Boogie2 language report
// (stuff where resolution succeeds, but typechecking might fail)

type C, D;

var x : int;
var y : int;
var z : int;
var a : [int]int;
var b : [int][C, D]int;

procedure P(i:int, j:int, m:C, n:D) returns () modifies x, y, a, b; {
  x := x+1;
  a[i] := 12;
  x, y := y, x;
  x, a[i] := x+1, x;
  x := true;            // type error
  a[true] := 5;         // type error

  z := 23;              // assignment to non-modifiable variable
  b[i][m, n] := 17;
  b[i][m, n], x := a[x], y;
}