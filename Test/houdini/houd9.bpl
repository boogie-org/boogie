// RUN: %parallel-boogie -contractInfer -printAssignment "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Houdini is very interactive and doesn't work with batch mode
// SKIP-WITH-PARAM: -proverOpt:BATCH_MODE=true
const {:existential true} b1:bool;
const {:existential true} b2:bool;
const {:existential true} b3:bool;

axiom(b1 && b2 && b3);

var fooVar: int;
var xVar: int;


procedure foo() 
modifies fooVar;
modifies xVar;
ensures b1 ==> fooVar>0;
ensures b2 ==> fooVar==0;
ensures b3 ==> xVar<0;
{
  fooVar:=5; 
  assert(fooVar>5);
  xVar:=0;
  assert(xVar>0);
}

// expected outcome: Errors
// expected assigment: b1->True,b2->True,b3->True







