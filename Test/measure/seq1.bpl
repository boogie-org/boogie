// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var x: int;
var y: int;

procedure one(tid: int, next: bool, abc: int) 
measure x;
measure x-1; 
{
    call two(2);
    call one(3, true, 2);
}

procedure two(tid: int)
measure x - 100;
measure y - 100;
{
   call three(2);
}

procedure three(tid: int)
measure x - 50;
measure x +10;
measure x + 20;
{
   call one(2, true, 4);
}

