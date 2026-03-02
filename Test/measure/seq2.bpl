// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var x: int;
var y: int;
var z: bool;

procedure one(tid: int, next: bool, abc: int) returns (out: bool)
measure x;
measure x-1; 
measure x+1;
modifies x;
{
    call two(2);
}

procedure two(tid: int)
measure y+1;
{
}

