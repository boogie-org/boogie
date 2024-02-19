// RUN: %parallel-boogie -lib:base "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype A { A({:linear} x: One int) }

procedure P0(a: A) returns ({:linear} a': One A) {
    a' := One(a);
}

procedure P1({:linear_in} a: A) returns ({:linear} a': A) {
    a' := a;
    a'->x := One(0);
}

procedure P2({:linear_in} a: A) returns ({:linear} a': A) {
    a'->x := a->x;
}

procedure P3({:linear} a: int) returns ({:linear} a': int) {
    a' := a;
}

procedure P4(a: int) returns ({:linear} a': int) {
    a' := a;
}