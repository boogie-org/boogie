// RUN: %boogie -noinfer -contractInfer -printAssignment -abstractHoudini:IA[ConstantProp] "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function {:existential true} b1():bool;
function {:existential true} b2():bool;
function {:existential true} b3():bool;

var myVar: int;

procedure foo(i:int) 
modifies myVar;
ensures b1() || myVar>0;
ensures b2() || myVar==0;
ensures b3() || myVar<0;
{
  myVar:=5; 
}

// expected assigment: b1->false,b2->true,b3->true













