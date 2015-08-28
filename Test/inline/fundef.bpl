// RUN: %boogie -print:- -env:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function {:inline true} foo(x:int) returns(bool)
  { x > 0 }
function {:inline false} foo2(x:int) returns(bool)
  { x > 0 }
function foo3(x:int) returns(bool)
  { x > 0 }
