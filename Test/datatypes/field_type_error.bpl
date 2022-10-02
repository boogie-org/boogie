// RUN: %parallel-boogie /monomorphize "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type{:datatype} Split _ _;
function{:constructor} Left<T, U>(i: T, j: U): Split T U;
function{:constructor} Right<X, Y>(i: Y, k: X): Split X Y;
