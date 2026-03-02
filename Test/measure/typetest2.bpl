// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var x: int;
var y: int;
var z : int;

yield left procedure {:layer 1} one(tid: int, next: bool, abc: int)
measure {:layer 1} tid;
{
    if (tid == 1)
    {
        return;
    }
    else 
    {
        call two(tid - 1, true, 2);
    }
}

yield left procedure {:layer 1} two(tid: int, next: bool, abc: int)
measure {:layer 1} tid;
measure {:layer 1} x;
{
    if (tid == 1)
    {
        return;
    }
    else 
    {
        async call {:sync} K();
        call one(tid - 1, true, 2);
    }
}

pure procedure A();

pure procedure B(k: int) 
measure {:layer 1} k;
{
    call A();
}

yield left procedure {:layer 1} K(){
}
