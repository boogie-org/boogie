// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// test for use of type synonyms

datatype Foo<T> { Mk(x: T) }

function foo<T>(): Foo T;

type Foo_int = Foo int;
type Foo_bool = Foo bool;

procedure p() {
  var x: Foo_int;
  var y: Foo_bool;
  x := Mk(1);
  y := Mk(false);
  assert x->x == 1;
  assert y->x == false;
}
