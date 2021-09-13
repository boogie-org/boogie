// We use boogie instead of parallel-boogie here to fix the order of the output from /printNecessaryAssumes
// RUN: %boogie /printNecessaryAssumes "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure test0(n: int)
{
    assume {:id "s0"} 0 < n;
    assume {:id "s0"} 0 < n;
}

procedure test1(n: int)
{
    assume {:id "s0"} 0 < n;
}
