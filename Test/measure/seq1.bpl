// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var x: int;
var y: int;
var z : int;

procedure one(tid: int, next: bool, abc: int) 
measure x;
measure x-1; 
{
    call two(2);
   //  call one(3, true, 2);
}

procedure two(tid: int)
measure y;
measure y - 1;
{
   // call three(2);
   call one(3, true, 2);
}

// procedure three(tid: int)
// measure z;
// {
//    call one(2, true, 4);
// }

