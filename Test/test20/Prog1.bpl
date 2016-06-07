// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Let's test some Boogie 2 features ...

type elements;

type Field a;
var heap : <a> [ref, Field a] a;



procedure p (x:int, y:ref, z:<a> [ref, Field a] a) returns (newHeap : <a> [ref, Field a] a) {

  var f : Field int;
  var g : Field bool;

  var heap : <a> [ref, Field a] a;
  
  assert z[y, f] >= 0;
  assert z[x, f] >= 0;   // error: x has wrong type
  assert z[y, x] >= 0;   // error: x has wrong type
  assert z[y, g] >= 0;   // error: result of map select has wrong type

  heap[y, g] := false;

}

type ref;
