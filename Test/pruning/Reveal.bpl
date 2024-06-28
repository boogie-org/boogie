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

/* hide P {
 *   hide * {
 *
 *   }
 *   P hidden.
 * }
 */