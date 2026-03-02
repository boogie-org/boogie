// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var x: int;

procedure one(tid: int, next: bool, abc: int) 
measure x;
{
    call one(2, true, 3);
}

