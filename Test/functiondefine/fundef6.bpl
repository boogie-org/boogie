// RUN: %parallel-boogie -print:- -env:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function {:define} foo(x:int) returns(bool)
  { x > 0 }
function {:define true} foo1(x:int) returns(bool)
  { x > 0 }
function {:define false} foo2(x:int) returns(bool)
  { x > 0 }
function foo3(x:int) returns(bool)
  { x > 0 }
