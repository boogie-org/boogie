// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type X;
const nil: X;
var {:layer 0,1} l: X;
var {:layer 0,1} x: int;
var {:layer 0,1}{:linear} unallocated: Set (One X);

yield procedure {:layer 1} Allocate() returns ({:linear} xl: One X)
ensures {:layer 1} xl->val != nil;
{
    call xl := AllocateLow();
}

yield procedure {:layer 1} main()
{
    var tid: One X;
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

atomic action {:layer 1} AtomicAllocateLow() returns ({:linear} xl: One X)
modifies unallocated;
{ assume xl->val != nil; assume Set_Contains(unallocated, xl); call One_Get(unallocated, xl); }

yield procedure {:layer 0} AllocateLow() returns ({:linear} xl: One X);
refines AtomicAllocateLow;

yield procedure {:layer 1} foo({:linear_in} tid: One X, val: int)
requires {:layer 1} tid->val != nil;
{
    call Lock(tid->val);
    call Yield(tid, l, x);
    call Set(val);
    call Yield(tid, l, x);
    assert {:layer 1} x == val;
    call Yield(tid, l, x);
    call Unlock();
}

yield invariant {:layer 1} Yield({:linear} tid: One X, old_l: X, old_x: int);
preserves tid->val != nil;
preserves old_l == tid->val ==> old_l == l && old_x == x;
