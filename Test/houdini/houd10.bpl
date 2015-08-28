// RUN: %boogie -noinfer -contractInfer -printAssignment "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
const {:existential true} b1:bool;
const {:existential true} b2:bool;
const {:existential true} b3:bool;

var fooVar: int;
var xVar: int;

procedure foo() 
modifies fooVar;
modifies xVar;
ensures b1 ==> fooVar==0;
ensures b3 ==> xVar<0;
{
  fooVar:=5; 
  call bar();
}

procedure bar(); 
modifies xVar;
requires fooVar!=5;

// expected outcome: Errors
// expected assigment: b1->True,b2->True,b3->True
