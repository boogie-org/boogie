// RUN: %parallel-boogie -monomorphize -normalizeNames:1 -enhancedErrorMessages:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Issue #361

type {:datatype} Cell _;
function {:constructor} Cell<T>(x: T): Cell T;

type {:datatype} OtherCell _;
function {:constructor} OtherCell<T>(x: T): OtherCell T;

function foo<T>(): Cell T;

procedure p() {
  var x: Cell (OtherCell int);
  x := Cell(OtherCell(1));
  assume {:print "x=", x} true;
  assert x#OtherCell(x#Cell(x)) == 1;
}

procedure q() {
  var x: Cell (OtherCell int);
  x := Cell(OtherCell(1));
  assume {:print "x=", x} true;
  assert x#OtherCell(x#Cell(x)) == 0;
}
