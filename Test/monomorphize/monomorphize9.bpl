// RUN: %parallel-boogie -monomorphize "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Issue #357

type {:datatype} Cell _;
function {:constructor} Mk<T>(i: int, x: T): Cell T;

procedure p() { }
