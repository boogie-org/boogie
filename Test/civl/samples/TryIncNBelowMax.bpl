// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0, 2} count: int;
const max: int;

yield procedure {:layer 1} TryIncBelowMax() returns (ok: bool)
preserves call Yield1();
refines atomic action {:layer 2} _ {
    if (ok) {
        assume count < max;
        count := count + 1;
    }
}
{
    var limit: int;

    call limit := ComputeLimit() | Yield1();
    assert {:layer 1} limit >= 0;
    async call BackgroundMaintenance();
    call ok := HelperInc(0, limit);
}

yield procedure {:layer 1} HelperInc(tries: int, limit: int) returns (ok: bool)
preserves call Yield1();
refines atomic action {:layer 2} _ {
    if (ok) {
        assume count < max;
        count := count + 1;
    }
}
{
    var n: int;

    if (tries >= limit) {
        ok := false; // limit reached
        return;
    }

    call n := Read();
    if (n >= max) {
        ok := false; 
        return;
    }

    call Yield1();

    call ok := CAS(n, n+1);
    if (ok) {
        return;
    }
    call ok := HelperInc(tries+1, limit);
    assert {:layer 1} count <= max;
}

yield procedure {:layer 1} ComputeLimit() returns (limit: int);
refines atomic action {:layer 2} _ { }
ensures {:layer 1} limit >= 0;

yield procedure {:layer 1} BackgroundMaintenance()
preserves call Yield1();
{
    assert {:layer 1} count <= max; 
}

yield procedure {:layer 0} CAS(prev: int, next: int) returns (status: bool);
refines atomic action {:layer 1} _ {
    assert prev < max; 
    status := (count == prev); 

    if (status) {
        count := next;
        status := true;
    } 
}

yield procedure {:layer 0} Read() returns (val: int);
refines atomic action {:layer 1} _ {
    assert count <= max;
    val := count;
}

yield invariant {:layer 1} Yield1();
preserves count <= max;