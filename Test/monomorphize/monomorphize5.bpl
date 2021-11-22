// RUN: %parallel-boogie -monomorphize -normalizeNames:1 -enhancedErrorMessages:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Issue #359

type {:datatype} Cell _;
function {:constructor} Mk<T>(x: T): Cell T;

function foo<T>(): Cell T;

procedure p() {
  var x: Cell int;
  x := Mk(1);
  assume {:print "x=", x} true;
  assert x#Mk(x) == 1;
}

procedure q() {
  var x: Cell int;
  x := Mk(1);
  assume {:print "x=", x} true;
  assert x#Mk(x) == 0;
}
