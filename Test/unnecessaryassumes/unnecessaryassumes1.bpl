// We use boogie instead of parallel-boogie here to fix the order of the output from /trackVerificationCoverage
// RUN: %boogie -trackVerificationCoverage -trace "%s" > "%t"
// RUN: %OutputCheck "%s" --file-to-check="%t"
// CHECK: Covered elements: s0
// CHECK: Covered elements: s2, s3
// CHECK: Elements covered by verification: s0, s2, s3
// UNSUPPORTED: batch_mode

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
