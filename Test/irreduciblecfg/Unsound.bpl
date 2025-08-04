// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure unsound() {
    var x: int;
    assume(x == 0);
    if (true) {
        goto Inside;
    }
    while (x < 10000) {
        Inside: x := x + 1;
    }

    assert(x == -1);
}