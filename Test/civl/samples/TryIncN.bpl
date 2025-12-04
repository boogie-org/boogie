// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var count: int;

yield procedure {:layer 1} TryIncN() returns (ok: bool)
refines atomic action {:layer 2} _{
    if (*) {
        count := count + 1;
    }
}
{
    var limit: int;

    call limit := ComputeLimit();
    // Start recursion with 0 retries
    call ok := HelperInc(0, limit);  
    return;
}


// Helper recursive procedure
yield procedure {:layer 1} HelperInc(tries: int, limit: int) returns (ok: bool)
refines atomic action {:layer 2} _{
    if (*) {
        count := count + 1;
    }
}
{
    var n: int;

    if (tries >= limit) {
        ok := false; // retry limit reached
        return; 
    }
    call n := Read();
    call Yield();
    call ok := CAS(n, n+1);
    if (ok) {
        return; // CAS succeeded
    }
    call ok := HelperInc(tries + 1, limit);
}


yield procedure {:layer 1} ComputeLimit() returns (limit: int)
refines AtomicComputeLimit;
{
   assume limit > 0;
}

action {:layer 2} AtomicComputeLimit() returns (limit: int) {
    assume limit > 0;
}



yield procedure {:layer 0} CAS(prev: int, next: int) returns (ok: bool);
refines atomic action {:layer 1} _ {
    ok := (count == prev);
    if (ok) {
        count := next;
    }
}

yield procedure {:layer 0} Read() returns (val: int); 
refines atomic action {:layer 1} _ {
    val := count;
}

yield invariant {:layer 1} Yield();