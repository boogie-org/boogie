// RUN: %boogie /printModel:4 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function may_fail(f: int) : bool;

procedure test0()
{
    var x: int;

    havoc x;
    assume 42 < x;
    assume {:minimize x} true;
    assert may_fail(x);
}

procedure test1()
{
    var x: int;

    x := 24;
    if (*) {
        x := 42;
    }
    assume {:minimize x} true;
    assert may_fail(x);
}

procedure test2()
{
    var x: int;

    x := 1;
    while (*) {
        x := x + 1;
    }
    assume {:minimize x} true;
    assert x < 10;
}

procedure test3()
{
    var x: int;

    havoc x;
    assume x < 42;
    assume {:maximize x} true;
    assert may_fail(x);
}

procedure test4()
{
    var x: int;

    x := 24;
    if (*) {
        x := 42;
    }
    assume {:maximize x} true;
    assert may_fail(x);
}

procedure test5()
{
    var x: int;

    x := 1;
    while (*) {
        x := x - 1;
    }
    assume {:maximize x} true;
    assert x < 1;
}

procedure test6()
{
    var x: int;

    x := 1;
    if (*) {
        x := 2;
    }
    assume {:maximize x} true;
    assert may_fail(x);
}
