// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// test for use of type synonyms

datatype Foo<T> { Foo(x: T) }

function foo<T>(): Foo T;

datatype Some { Some(x: int) }

type MyT = Some;

procedure p() {
    var c1: Foo MyT;
    var c2: Foo Some;
}
