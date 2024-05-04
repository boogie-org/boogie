// RUN: %parallel-boogie -normalizeNames:1 -enhancedErrorMessages:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Issue #359

datatype Foo<T> { Mk(x: T) }


function foo<T>(): Foo T;

procedure p() {
  var x: Foo int;
  x := Mk(1);
  assume {:print "x=", x} true;
  assert x->x == 1;
}

procedure q() {
  var x: Foo int;
  x := Mk(1);
  assume {:print "x=", x} true;
  assert x->x == 0;
}
