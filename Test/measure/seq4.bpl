// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var x: int;
var y: int;
var z : int;

procedure two(tid: int, cid: int)
measure tid + x;
measure cid;
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

procedure one(tid: int, cid: int)
measure tid;
measure cid;
{
    if (tid <= 1 || cid <= 1)
    {
        return;
    }
    else 
    {
        call two(tid - 1, cid - 1);
    }
}
