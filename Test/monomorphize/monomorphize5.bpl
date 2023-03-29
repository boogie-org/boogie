// RUN: %parallel-boogie -monomorphize -normalizeNames:1 -enhancedErrorMessages:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Issue #359

datatype Cell<T> { Mk(x: T) }


function foo<T>(): Cell T;

procedure p() {
  var x: Cell int;
  x := Mk(1);
  assume {:print "x=", x} true;
  assert x->x == 1;
}

procedure q() {
  var x: Cell int;
  x := Mk(1);
  assume {:print "x=", x} true;
  assert x->x == 0;
}
