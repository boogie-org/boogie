// RUN: %parallel-boogie -monomorphize "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Issue #357

datatype Cell<T> { Mk(x: T) }

procedure p() { }
