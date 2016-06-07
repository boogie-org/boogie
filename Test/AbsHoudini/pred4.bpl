// RUN: %boogie -noinfer -contractInfer -printAssignment -inlineDepth:1 -abstractHoudini:PredicateAbs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function {:existential true} b1(x:bool, y:bool): bool;
function {:existential true} {:absdomain "Intervals"} b3(x:int): bool;

var g: int;

procedure main()
modifies g;
{
  g := 0;
  if(*) { g := 5; }
  call foo();
}

procedure foo()
  modifies g;
  requires b1(g == 0, g == 5);
  ensures b3(g);
{
  assume g != 5;
}

