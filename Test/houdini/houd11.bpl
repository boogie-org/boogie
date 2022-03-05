// RUN: %parallel-boogie -contractInfer -printAssignment "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Houdini is very interactive and doesn't work with batch mode
// SKIP-WITH-PARAM: -proverOpt:BATCH_MODE=true

var fooVar: int;

procedure foo() 
modifies fooVar;
{
  fooVar:=5; 
  assert(fooVar==4);
  assert(fooVar==3);
}

// expected outcome: Errors
// expected assigment: []
