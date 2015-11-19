// RUN: %boogie /printModel:4 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure test0()
{
    var x: int;

    assume x < 42;
    assume {:maximize x} true; // TODO(wuestholz): Currently, Z3 does not produce a model with "x == 41" here. It seems like this is due to the fact that it returns "unknown".
    assert (exists y: int :: y < x);
}

procedure test1()
{
    var x: int;

    assume x < 42;
    assume {:maximize x} true;
    assert (forall y: int :: y < x);
}
