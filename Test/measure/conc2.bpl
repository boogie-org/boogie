// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var x: int;
var y: int;
var z : int;

yield left procedure {:layer 1} two(tid: int, next: bool, abc: int)
measure {:layer 1} x;
{
    if (tid == 1)
    {
        return;
    }
    else 
    {
        call two(tid-1, true, 3);
    }
}


