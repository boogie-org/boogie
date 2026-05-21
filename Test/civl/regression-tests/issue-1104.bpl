// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var x: int;

yield left procedure {:layer 1} two(tid: int, cid: int)
preserves {:layer 1} x > 0;
{
    if (tid <= 1 || cid <=1 )
    {
        return;
    }
    else 
    {
        call one(tid - 1, cid - 1);
    }
}

yield left procedure {:layer 1} one(tid: int, cid: int)
preserves {:layer 1} x > 0;
{
    if (tid <= 1 || cid <= 1)
    {
        return;
    }
    else 
    {
        assert {:layer 1} false;
        call two(tid - 1, cid - 1);
    }
}