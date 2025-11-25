// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0, 2} count: int;
const retry_limit: int;

yield procedure {:layer 1} TryInc() returns (ok: bool)
refines atomic action {:layer 2} _ {
    ok := false;
    if(*) {
        count := count + 1;
        ok := true;
    }
}
{
    var n: int;
    ok := false;
    call n := Read();
    call Yield();
    call ok := CAS(n, n+1);
    return;
}


yield procedure {:layer 0} CAS(prev: int, next: int) returns (status: bool);
refines atomic action {:layer 1} _ {
    if (count == prev) {
        count := next;
        status := true;
    } else {
        status := false;
    }
}

yield procedure {:layer 0} Read() returns (val: int);
refines atomic action {:layer 1} _ {
    val := count;
}

yield invariant {:layer 1} Yield();
