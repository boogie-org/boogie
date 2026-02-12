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
{

}

procedure three(tid: int)

{

}

