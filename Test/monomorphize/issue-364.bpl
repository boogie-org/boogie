// RUN: %parallel-boogie /monomorphize "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// test for use of type synonyms

type {:datatype} Cell _;
function {:constructor} Cell<T>(x: T): Cell T;

function foo<T>(): Cell T;

type {:datatype} Some;
function {:constructor} Some(x: int): Some;

type MyT = Some;

procedure p() {
    var c1: Cell MyT;
    var c2: Cell Some;
}
