// RUN: %boogie -noinfer -contractInfer -printAssignment -abstractHoudini:IA[ConstantProp] "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function {:existential true} b1():bool;
function {:existential true} b2():bool;
function {:existential true} b3():bool;
function {:existential true} Assert(): bool;
var fooVar: int;
var xVar: int;

procedure foo() 
modifies fooVar;
modifies xVar;
ensures b1() || fooVar==0;
ensures b3() || xVar<0;
{
  fooVar:=5; 
  call bar();
}

procedure bar(); 
modifies xVar;
requires Assert() || fooVar!=5;

// expected assigment: Assert->true,b1->True,b2->false,b3->True
