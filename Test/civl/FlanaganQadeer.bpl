// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type {:linear "tid"} X;
const nil: X;
var {:layer 0,1} l: X;
var {:layer 0,1} x: int;
var {:layer 0,1}{:linear "tid"} unallocated:[X]bool;

yield procedure {:layer 1} Allocate() returns ({:linear "tid"} xl: X)
ensures {:layer 1} xl != nil;
{
    call xl := AllocateLow();
}

yield procedure {:layer 1} main()
{
    var {:linear "tid"} tid: X;
    var val: int;

    while (*)
    invariant {:yields} true;
    {
        call tid := Allocate();
        havoc val;
        async call foo(tid, val);
    }
}

atomic action {:layer 1} AtomicLock(tid: X)
modifies l;
{ assume l == nil; l := tid; }

yield procedure {:layer 0} Lock(tid: X);
refines AtomicLock;

atomic action {:layer 1} AtomicUnlock()
modifies l;
{ l := nil; }

yield procedure {:layer 0} Unlock();
refines AtomicUnlock;

atomic action {:layer 1} AtomicSet(val: int)
modifies x;
{ x := val; }

yield procedure {:layer 0} Set(val: int);
refines AtomicSet;

atomic action {:layer 1} AtomicAllocateLow() returns ({:linear "tid"} xl: X)
modifies unallocated;
{ assume xl != nil; assume unallocated[xl]; unallocated[xl] := false; }

yield procedure {:layer 0} AllocateLow() returns ({:linear "tid"} xl: X);
refines AtomicAllocateLow;

yield procedure {:layer 1} foo({:linear_in "tid"} tid: X, val: int)
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

yield invariant {:layer 1} Yield({:linear "tid"} tid: X, old_l: X, old_x: int);
invariant tid != nil;
invariant old_l == tid ==> old_l == l && old_x == x;
