// RUN: %boogie -noinfer -contractInfer -printAssignment -abstractHoudini:IA[ConstantProp] "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function {:existential true} b1():bool;
function {:existential true} b2():bool;
function {:existential true} b3():bool;
function {:existential true} Assert(): bool;
var myVar: int;

procedure foo(i:int) 
requires b1() || i>0;
requires b2() || i==0;
requires b3() || i<0;
modifies myVar;
ensures Assert() || myVar>0;
{
  myVar:=5; 
}

procedure bar(i:int) 
modifies myVar;
{
  call foo(5);
}
// expected outcome: Correct
// expected Assigment: Assert = false, b1->false,b2->true,b3->true












