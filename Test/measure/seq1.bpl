// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var x: int;
var y: int;

procedure one(tid: int, next: bool, abc: int) 
measure x;
measure x-1; 
{
    call one(2, true,3 );
}

procedure two(tid: int)
measure y+1;
{

}

