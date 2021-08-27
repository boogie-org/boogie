// RUN: %parallel-boogie  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:inline} foo(x:int) returns(int);

function {:define} bar(x:int) returns(int);
