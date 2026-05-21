// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var count: int;

yield procedure {:layer 1} TryInc() returns (ok: bool)
refines AtomicTryInc;
{
    var n: int;
    
    ok := false;
    call n := Read();
    call Yield();
    call ok := CAS(n, n+1);
}

atomic action {:layer 2} AtomicTryInc() returns (ok: bool) {
    if (*) {
        count := count + 1;
    }
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