// RUN: %boogie -noinfer -contractInfer -printAssignment "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
const {:existential true} b1:bool;
const {:existential true} b2:bool;
const {:existential true} b3:bool;

var myVar: int;

procedure foo(i:int) 
requires b1 ==> i>0;
requires b2 ==> i==0;
requires b3 ==> i<0;
modifies myVar;
ensures myVar>0;
{
  myVar:=5; 
}

procedure bar(i:int) 
modifies myVar;
{
  call foo(5);
}
// expected outcome: Correct
// expected Assigment: b1->True,b2->False,b3->False












