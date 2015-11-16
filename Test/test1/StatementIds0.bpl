// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure test0(n: int)
{
    assume {:id "s0"} true;
    assert {:id "s0"} true;
}

procedure test1()
{
    call {:id "s0"} P();
}

procedure test2(n: int)
{
    while (*)
      invariant {:id "s0"} true;
      invariant {:id "s0"} true;
    {
    }
}

procedure P();
