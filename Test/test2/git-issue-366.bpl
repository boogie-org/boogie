// RUN: %parallel-boogie -rlimit:5 /proverOpt:O:smt.qi.eager_threshold=100 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function f(i:int, j:int) returns (int)
{
    if i == 0 then 0 else f(i - 1, i * j + 1) + f(i - 1, 2 * i * j)
}

procedure test0(x:int)
{
    assert(x - x == 0);
}

procedure {:rlimit 100000000} test1()
{
    assert(f(13,5) == 0);
}
