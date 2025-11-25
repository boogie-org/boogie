// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0, 2} count: int;

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
    var success: bool;
    var retry_limit: int;

    call retry_limit := ComputeLimit();
    call ok :=  HelperInc(0, retry_limit);  // Start recursion with 0 retries
    return;
}

yield procedure {:layer 1} ComputeLimit() returns (retry_limit: int)
{
   assume retry_limit > 0;
}

// Helper recursive procedure
yield procedure {:layer 1} HelperInc(tries: int, retry_limit: int) returns (ok: bool)
refines atomic action {:layer 2} _ {
    ok := false;
    if(*) {
        count := count + 1;
        ok := true;
    }
}
{
    var n: int;
    var success: bool;

    if (tries > retry_limit) {
        ok := false; // retry limit reached
        return; 
    }

    call n := Read();
    call Yield();
    call success := CAS(n, n+1);

    if (success) {
        ok := true;
        return; // CAS succeeded
    }

    call ok := HelperInc(tries + 1, retry_limit); // CAS failed => recurse with incremented retry count
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
