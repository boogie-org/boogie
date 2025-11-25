// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0, 2} count: int;
const retry_limit: int;

yield procedure {:layer 1} TryInc()
refines atomic action {:layer 2} _ {
    if(*) {
        count := count + 1;
    }
}
{
    var n: int;
    var success: bool;

    // Start recursion with 0 retries
    call HelperInc(0);
    return;
}

// Helper recursive procedure
yield procedure {:layer 1} HelperInc(tries: int)
refines atomic action {:layer 2} _ {
    if(*) {
        count := count + 1;
    }
}
{
    var n: int;
    var success: bool;

    if (retry_limit > tries) {
        return; // retry limit reached
    }

    call n := Read();
    call Yield();
    call success := CAS(n, n+1);

    if (success) {
        return; // CAS succeeded
    }

    // CAS failed => recurse with incremented retry count
    call HelperInc(tries + 1);
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
