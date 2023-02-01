// RUN: %parallel-boogie /monomorphize "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// test for use of type synonyms

datatype Cell<T> { Cell(x: T) }

function foo<T>(): Cell T;

datatype Some { Some(x: int) }

type MyT = Some;

procedure p() {
    var c1: Cell MyT;
    var c2: Cell Some;
}
