// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype X {
    A'(a: int),
    B'(b: bool)
}

procedure P(x: X) {
    assume x is A';
    assert !(x is B');
}
