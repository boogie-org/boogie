// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var x: int;
var y: int;
var z : int;

yield procedure {:layer 1} one(tid: int, next: bool, abc: int) 
measure {:layer 1} x;
measure {:layer 1} x-1; 
{
   //  call two(2);
    call one(3, true, 2);
}

// yield procedure {:layer 1} two(tid: int)
// measure  y;
// measure y - 1;
// {
//    // call three(2);
//    // call one(3, true, 2);
// }

// procedure three(tid: int)
// measure z;
// {
//    call one(2, true, 4);
// }

