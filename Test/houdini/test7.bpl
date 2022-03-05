// RUN: %parallel-boogie -contractInfer -printAssignment -inlineDepth:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Houdini is very interactive and doesn't work with batch mode
// SKIP-WITH-PARAM: -proverOpt:BATCH_MODE=true
var g: int;

procedure main() 
modifies g;
{
  g := 0;
  call foo();
  assert g == 1;
}

procedure foo() 
modifies g;
{
  g := g + 1;
}
