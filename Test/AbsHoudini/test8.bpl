// RUN: %boogie -noinfer -contractInfer -printAssignment -inlineDepth:1 -abstractHoudini:IA[ConstantProp] "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function {:existential true} Assert(): bool;

var g: int;

procedure main() 
modifies g;
{
  g := 0;
  call foo();
  assert Assert() || g == 1;
}

procedure {:inline 1} foo() 
modifies g;
{
  call bar();
}

procedure bar()
modifies g;
{
  g := g + 1;
}

// Expected: Assert = false
