// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Issue #361

datatype Foo<T> { Foo(x: T) }


datatype OtherFoo<T> { OtherFoo(x: T) }


function foo<T>(): Foo T;

procedure p() {
  var x: Foo (OtherFoo int);
  x := Foo(OtherFoo(1));
  assume {:print "x=", x} true;
  assert x->x->x == 1;
}

procedure q() {
  var x: Foo (OtherFoo int);
  x := Foo(OtherFoo(1));
  assume {:print "x=", x} true;
  assert x->x->x == 0;
}
