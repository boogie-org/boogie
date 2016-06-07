// RUN: %boogie /printModel:4 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure test0()
{
    var x: int;

    assume x < 42;
    assume {:maximize x} true;
    assert (exists y: int :: y < x);
}

procedure test1()
{
    var x: int;

    assume x < 42;
    assume {:maximize x} true;
    assert (forall y: int :: y < x);
}
