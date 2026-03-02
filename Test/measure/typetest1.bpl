// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var x: int;
var y: int;
var z : int;

yield procedure {:layer 1} one(tid: int, next: bool, abc: int)
measure  {:layer 1} tid;
{
    if (tid == 1)
    {
        return;
    }
    else 
    {
        call one(tid - 1, true, 2);
    }
}