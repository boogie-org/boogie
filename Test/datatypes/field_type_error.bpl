// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Split<X, Y> {
  Left(i: X, j: Y),
  Right(i: Y, k: X)
}
