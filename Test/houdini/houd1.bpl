// RUN: %boogie -noinfer -contractInfer -printAssignment "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
const {:existential true} b1:bool;

var myVar: int;

procedure foo (i:int)
modifies myVar;
// comment
ensures b1 ==> myVar>0;
ensures myVar!=-1;
{
  if (i>0) {
    myVar := 5;
  } else {
    myVar := 0;
  }
}

// expected output: Correct
// expected end assigment: b1->False 
