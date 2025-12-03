// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0, 2} count: int;
const limit: int;

yield procedure {:layer 1} TryIncBelowLimit() returns (ok: bool)
requires call Yield1();
refines atomic action {:layer 2} _ {
    if (ok) {
        assume count < limit;
        count := count + 1;
    }
}
{
    var n: int;
    var success: bool;

    call Yield1();

    call n := Read();

    if (n >= limit) {
        ok := false; 
        return; 
    }

    call Yield1();

    call ok := CAS(n, n+1);

    if (ok) {
        return;
    }

    call ok := TryIncBelowLimit();
}

yield procedure {:layer 0} CAS(prev: int, next: int) returns (status: bool);
refines atomic action {:layer 1} _ {
    assert prev < limit; 
    if (count == prev) {
        count := next;
        status := true;
    } else {
        status := false;
    }
}

yield procedure {:layer 0} Read() returns (val: int);
refines atomic action {:layer 1} _ {
    assert count <= limit;
    val := count;
}

yield invariant {:layer 1} Yield1();
preserves count <= limit;



