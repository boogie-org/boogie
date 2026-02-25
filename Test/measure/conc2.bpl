// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var x: int;
var y: int;
var z : int;

yield left procedure {:layer 1} two(tid: int, next: bool, abc: int)
requires {:layer 1} tid > 0;
measure {:layer 1} tid;
{
    if (tid == 1)
    {
        return;
    }
    else 
    {
        assume (tid - 1) > 0;
        call two(tid - 1, true, 3);
    }
}


// yield left procedure {:layer 1} one(tid: int, next: bool, abc: int)
// measure {:layer 1} y;
// {
//     if (tid == 1)
//     {
//         return;
//     }
//     else 
//     {
//         call one(tid-1, true, 3);
//     }
// }


// all are greater than or equal to 0 and atleast one of them is greater than 0