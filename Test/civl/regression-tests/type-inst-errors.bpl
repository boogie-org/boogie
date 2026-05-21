// RUN: %parallel-boogie -lib:base "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype A<T> { A(x: One T) }

procedure P0(a: A int) returns ({:linear} b: One (A int)) {
    b := One(a);
}

procedure P1(a: Map (A int) int) {

}

