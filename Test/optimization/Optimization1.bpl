// RUN: %boogie /noVerify /printModel:4 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure test0(n: int)
{
    assume {:minimize} true;
}

procedure test1(n: int)
{
    assume {:maximize} true;
}

procedure test2(n: int)
{
    assume {:minimize n, n} true;
}

procedure test3(n: int)
{
    assume {:maximize n, n} true;
}

procedure test4(n: int)
{
    assume {:minimize true} true;
}

procedure test5(n: int)
{
    assume {:maximize true} true;
}
