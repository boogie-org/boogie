// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Split<T> {
  Left(i: T),
  Left(i: T)
}
