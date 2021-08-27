// RUN: %parallel-boogie  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var M:[int]int;
function {:define} store(M:[int]int, p:int, i:int) returns ([int]int) { M[p := i] }

procedure test(ArgM:[int]int) returns (r:int)
  ensures r == 20;
{
  var i:int;
  var M:[int]int;
  M := ArgM;
  M[i] := 10;
  M := store(M, i, 20);
  r := M[i];
}
