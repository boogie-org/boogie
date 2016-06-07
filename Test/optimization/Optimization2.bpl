// RUN: %boogie /noVerify /printModel:4 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure test0(n: int)
{
    assume {:minimize true} true;
}

procedure test1(n: int)
{
    assume {:maximize true} true;
}
