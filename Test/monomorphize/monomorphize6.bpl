// RUN: %parallel-boogie -monomorphize "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Issue #361

datatype Cell<T> { Cell(x: T) }


datatype OtherCell<T> { OtherCell(x: T) }


function foo<T>(): Cell T;

procedure p() {
  var x: Cell (OtherCell int);
  x := Cell(OtherCell(1));
  assume {:print "x=", x} true;
  assert x->x->x == 1;
}

procedure q() {
  var x: Cell (OtherCell int);
  x := Cell(OtherCell(1));
  assume {:print "x=", x} true;
  assert x->x->x == 0;
}
