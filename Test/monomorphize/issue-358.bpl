// RUN: %parallel-boogie /monomorphize "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// test for use of type synonyms

type {:datatype} Cell _;
function {:constructor} Mk<T>(x: T): Cell T;

function foo<T>(): Cell T;

type Cell_int = Cell int;
type Cell_bool = Cell bool;

procedure p() {
  var x: Cell_int;
  var y: Cell_bool;
  x := Mk(1);
  y := Mk(false);
  assert x#Mk(x) == 1;
  assert x#Mk(y) == false;
}
