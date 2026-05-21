// RUN: %parallel-boogie -inferModifies "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var x: int;

procedure A()
requires x == 0;
{
    call B();
    assert x == 0; // should fail
}

procedure B()
{
    if (*) {
        x := x + 1;
    } else {
        call C();
    }
}

procedure C() {
    if (*) {
        call B();
    }
}