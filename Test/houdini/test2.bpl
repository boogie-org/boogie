// RUN: %boogie -noinfer -contractInfer -printAssignment -inlineDepth:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var g: int;
var h: int;

procedure foo() 
modifies g, h;
ensures b0 ==> old(g) == g;
{
  call AcquireLock();
  call ReleaseLock();
}

procedure AcquireLock()
modifies g, h;
ensures b1 ==> old(g) == g;
{
  h := g;
  g := 1;
}

procedure ReleaseLock()
modifies g, h;
ensures b2 ==> old(g) == g;
{
  g := h;
}

procedure main()
modifies g, h;
{
  g := 0;
  call foo();
  assert g == 0;
}

const {:existential true} b0: bool;
const {:existential true} b1: bool;
const {:existential true } b2: bool;

