// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0, 2} count: int;

action {:layer 2} AtomicInc()
modifies count;
{
    count := count + 1;
}
yield procedure {:layer 1} Inc() refines AtomicInc {
    var n: int;
    var success: bool;

    while(true)
    invariant {:yields} true;
    {
        call n := Read();
        call Yield();
        call success := CAS(n, n+1);
        if (success) {
            break;
        }
    }
}

action {:layer 1} AtomicCAS(prev: int, next: int) returns (status: bool)
modifies count;
{
    if (count == prev) {
        count := next;
        status := true;
    } else {
        status := false;
    }
}
yield procedure {:layer 0} CAS(prev: int, next: int) returns (status: bool) refines AtomicCAS;

action {:layer 1} AtomicRead() returns (val: int)
{
    val := count;
}
yield procedure {:layer 0} Read() returns (val: int) refines AtomicRead;

yield invariant {:layer 1} Yield();
