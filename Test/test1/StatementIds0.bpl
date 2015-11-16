// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure test0(n: int)
{
    assume {:id "s0"} 0 < n;
    assert {:id "s0"} 0 < n;
}

procedure test1(n: int)
{
    call {:id "s0"} P();
}

procedure P();
