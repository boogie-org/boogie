// RUN: %parallel-boogie /monomorphize "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// test for use of cycle of increasing types

type {:datatype} Option _;
function {:constructor} None<T>(): Option T;
function {:constructor} Some<T>(t: T): Option T;

function B<T>(i: T) : bool
{
    B(Some(i))
}
