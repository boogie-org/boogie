// RUN: %boogie -noinfer -contractInfer -printAssignment -inlineDepth:1 -abstractHoudini:PredicateAbs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function {:existential true} b0(x:bool): bool;

var g: int;

procedure main()
modifies g;
ensures b0(g == old(g));
{
  if(*) { g := 5; }
  assume g != 5;
}

