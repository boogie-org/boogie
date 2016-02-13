// RUN: %boogie /printNecessaryAssumes "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure test0(n: int)
{
    assume {:id "s0"} 0 < n;
    assert 0 <= n;  // verified under s0
}

procedure test1(n: int)
{
    assume 0 < n;
    assume {:id "s1"} n == 3;
    assert 0 <= n;  // verified under true
}

procedure test2(n: int)
{
    assume 0 < n;
    assume {:id "s2"} n <= 42;
    assume {:id "s3"} 42 <= n;
    assert n == 42;  // verified under s2 and s3
}
