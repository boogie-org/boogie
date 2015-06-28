// RUN: %boogie -noinfer -contractInfer -printAssignment -inlineDepth:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var g: bool;

procedure foo() 
modifies g;
ensures b0 ==> (!old(g) ==> old(g) == g);
{
  call AcquireLock();
  call ReleaseLock();
}

procedure AcquireLock()
modifies g;
ensures b1 ==> old(g) == g;
{
  g := true;
}

procedure ReleaseLock()
modifies g;
ensures b2 ==> old(g) == g;
{
  g := false;
}

procedure main()
modifies g;
{
  g := false;
  call foo();
  assert !g;
}

const {:existential true} b0: bool;
const {:existential true} b1: bool;
const {:existential true } b2: bool;

