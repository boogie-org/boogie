// RUN: %boogie -typeEncoding:n -logPrefix:0n "%s" > "%t"
// RUN: %diff "%s.n.expect" "%t"
// RUN: %boogie -typeEncoding:p -logPrefix:0p "%s" > "%t"
// RUN: %diff "%s.p.expect" "%t"
// RUN: %boogie -typeEncoding:a -logPrefix:0a "%s" > "%t"
// RUN: %diff "%s.a.expect" "%t"
// Examples from the Boogie2 language report

type C, D;

var x : int;
var y : int;
var z : int;
var a : [int]int;
var b : [int][C, D]int;

procedure P(i:int, j:int, m:C, n:D) returns () modifies x, y, a, b; {
  var x1 : int;
  var y1 : int;

  x := x+1;
  a[i] := 12;

  assert a[i] == 12;

  x1 := x;
  y1 := y;

  x, y := y, x;

  assert x == y1 && y == x1;
  assert x == x1;            // error

  x, a[i] := x+1, x;
  assert x == y1+1 && a[i] == y1;

  b[i][m, n] := 17;
  b[i][m, n], x := a[x], y;

  assert b[i][m, n] == a[y1+1];
  assert false;              // error
}

procedure Q() returns () modifies x, y, z; {

  x, y, z := 1, 2, 3;

  x, y, z := y, z, x;
  x, y, z := y, z, x;
  x, y, z := y, z, x;

  assert x == 1 && y == 2 && z == 3;

  x, y, z := y+1, z+1, x+1;
  x, y, z := y+1, z+1, x+1;
  x, y, z := y+1, z+1, x+1;

  assert x == 4 && y == 5 && z == 6;

  assert a[x] == a[y];    // error

}