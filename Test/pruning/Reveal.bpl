// RUN: %parallel-boogie /prune:1 /errorTrace:0 /vcsSplitOnEveryAssert "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function outer(x: int) : int uses {
  hideable axiom (forall x: int :: {outer(x)} outer(x) == inner(x) + 1);
}

function inner(x: int): int uses {
  hideable axiom (forall x: int :: {inner(x)} inner(x) == 42);
}
  
procedure Foo()
{
  var x: int;
  hide *;
  x := outer(3);
  if (*) {
    reveal outer;
    assert x == inner(3) + 1;
    if (*) {
      reveal inner;
      assert x == 43;
    } else {
      assert x == 43; // error can not prove
    }
  } else {
    reveal inner;
    if (*) {
      assert x == inner(3) + 1; // error can not prove
    } else {
      assert x == 43; // can not prove
    }
  }
}

procedure Scoping() {
  hide *;
  push;
  reveal outer;
  assert outer(2) == inner(2) + 1;
  pop;
  assert outer(3) == inner(3) + 1; // error
}

procedure Nesting() {
  hide *;
  push;
  push;
  if (*) {
    reveal outer;
  }
  pop;
  pop;
}

procedure HideSpecific() {
  hide inner;
  reveal inner;
  assert inner(3) == 42;
}

revealed function alwaysRevealed(x: int): int uses {
  hideable axiom (forall x: int :: {alwaysRevealed(x)} alwaysRevealed(x) == 42);
}

procedure AlwaysRevealed() {
  hide *;
  assert alwaysRevealed(3) == 42;
}