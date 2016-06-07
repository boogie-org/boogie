// RUN: %boogie -noinfer -contractInfer -printAssignment -abstractHoudini:IA[ConstantProp] "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function {:existential true} Assert() : bool;

var fooVar: int;

procedure foo() 
modifies fooVar;
{
  fooVar:=5; 
  assert Assert() || (fooVar==4);
  assert Assert() || (fooVar==3);
}

// expected assigment: Assert -> true
