// RUN: %boogie -noinfer -contractInfer -printAssignment -inlineDepth:1 -abstractHoudini:IA[ConstantProp] "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var g: bool;

procedure foo() 
modifies g;
ensures b0() || (!old(g) ==> old(g) == g);
{
  call AcquireLock();
  call ReleaseLock();
}

procedure AcquireLock()
modifies g;
ensures b1() || old(g) == g;
{
  g := true;
}

procedure ReleaseLock()
modifies g;
ensures b2() || old(g) == g;
{
  g := false;
}

procedure main()
modifies g;
{
  g := false;
  call foo();
  assert Assert() || !g;
}

function {:existential true} b0(): bool;
function {:existential true} b1(): bool;
function {:existential true } b2(): bool;
function {:existential true} Assert(): bool;

// Expected: b0 = false, b1 = true, b2 = true, Assert = false
