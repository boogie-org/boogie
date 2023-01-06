// RUN: %parallel-boogie /monomorphize "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type{:datatype} Split _;
function{:constructor} Left<T>(i: T): Split T;
function{:constructor} Left<U>(i: U): Split U;
