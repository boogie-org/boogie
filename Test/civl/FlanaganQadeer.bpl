// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type {:linear "tid"} X;
const nil: X;
var {:layer 0,1} l: X;
var {:layer 0,1} x: int;
var {:layer 0,1}{:linear "tid"} unallocated:[X]bool;

procedure {:yields} {:layer 1} Allocate() returns ({:linear "tid"} xl: X)
ensures {:layer 1} xl != nil;
{
    call xl := AllocateLow();
}

procedure {:yields} {:layer 1} main()
{
    var {:linear "tid"} tid: X;
    var val: int;

    while (*)
    invariant {:yields} {:layer 1} true;
    {
        call tid := Allocate();
        havoc val;
        async call foo(tid, val);
    }
}

procedure {:atomic} {:layer 1} AtomicLock(tid: X)
modifies l;
{ assume l == nil; l := tid; }

procedure {:yields} {:layer 0} {:refines "AtomicLock"} Lock(tid: X);

procedure {:atomic} {:layer 1} AtomicUnlock()
modifies l;
{ l := nil; }

procedure {:yields} {:layer 0} {:refines "AtomicUnlock"} Unlock();

procedure {:atomic} {:layer 1} AtomicSet(val: int)
modifies x;
{ x := val; }

procedure {:yields} {:layer 0} {:refines "AtomicSet"} Set(val: int);

procedure {:atomic} {:layer 1} AtomicAllocateLow() returns ({:linear "tid"} xl: X)
modifies unallocated;
{ assume xl != nil; assume unallocated[xl]; unallocated[xl] := false; }

procedure {:yields} {:layer 0} {:refines "AtomicAllocateLow"} AllocateLow() returns ({:linear "tid"} xl: X);

procedure {:yields} {:layer 1} foo({:linear_in "tid"} tid: X, val: int)
requires {:layer 1} tid != nil;
{
    call Lock(tid);
    call Yield(tid, l, x);
    call Set(val);
    call Yield(tid, l, x);
    assert {:layer 1} x == val;
    call Yield(tid, l, x);
    call Unlock();
}

procedure {:yield_invariant} {:layer 1} Yield({:linear "tid"} tid: X, old_l: X, old_x: int);
requires tid != nil;
requires old_l == tid ==> old_l == l && old_x == x;
