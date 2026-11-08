// RUN: %parallel-boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// A map has at least one index, so none of these parse.

var m: []int;
var p: <a>[]a;

procedure P(x: [int]int) returns (y: [int]int)
{
  y := x[];
  y := x[:= 0];
  y[] := 0;
}
