// RUN: %boogie -noinfer -contractInfer -printAssignment -abstractHoudini:IA[ConstantProp] "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function {:existential true} Assert(x:bool) : bool;
function {:existential true} b1 (x:bool):bool;
function {:existential true} b2 (x:bool):bool;


var myVar: int;

procedure bar(i:int) 
modifies myVar;
ensures Assert(myVar>0);
{
  call foo(5);
}

procedure foo (i:int)
modifies myVar;
ensures b1(myVar>0);
ensures Assert(myVar!=-1);
{
  if (i>0) {
    myVar := 5;
  } else {
    myVar := 0;
  }
}

// expected end assigment: Assert(x) = true, b1(x) = true, b2(x) = false
