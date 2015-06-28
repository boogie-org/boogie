// RUN: %boogie -noinfer -contractInfer -printAssignment -inlineDepth:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var g: int;

procedure main() 
modifies g;
{
  g := 0;
  call foo();
  assert g == 1;
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
