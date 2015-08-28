// RUN: %boogie -noinfer -contractInfer -printAssignment -inlineDepth:1 -abstractHoudini:PredicateAbs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function {:existential true} b0(x:bool, y:bool): bool;
function {:existential true} b1(x:bool, y:bool): bool;
function {:existential true} b2(x:bool, y:bool): bool;

var g: int;

procedure main()
modifies g;
ensures b0(g == 0, g == 5);
{
  assume 0 == old(g) || 1 == old(g);
  g := 0;
  if(*) { g := 5; }
  call foo();
}

procedure foo()
  modifies g;
  requires b1(g == 0, g == 5);
  ensures b2(old(g) == 0, old(g) == 5);
{
  assume g != 5;
}

