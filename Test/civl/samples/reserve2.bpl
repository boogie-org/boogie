// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*
This example models a memory allocator based on count of free cells (freeSpace) and an
array that keeps tracks of the allocation status of each cell (isFree). To allocate
a cell, freeSpace is decremented atomically, blocking to ensure that freeSpace does not
go below zero. If the decrement succeeds, then a scan of isFree is performed to find a
free cell. The goal of the verification is to prove that this scan will succeed. The
main challenge in the proof is to reason about cardinality of constructed sets.

The layer transformations are as follows:
1 -> 2: transform isFree array into the finite set isFreeSet enabling cardinality reasoning
2 -> 3: use cardinality reasoning to transform freeSpace into the bijection allocMap

The verification goal is discharged at layer 3.
*/

datatype Bijection {
  Bijection(tidToPtr: Map Tid int, ptrToTid: Map int Tid)
}

function {:inline} BijectionInvariant(allocMap: Bijection): bool {
    (forall tid: Tid ::
        Map_Contains(allocMap->tidToPtr, tid) ==>
            (var x := Map_At(allocMap->tidToPtr, tid); Map_Contains(allocMap->ptrToTid, x) && Map_At(allocMap->ptrToTid, x) == tid))
    &&
    (forall ptr: int ::
        Map_Contains(allocMap->ptrToTid, ptr) ==>
            (var x := Map_At(allocMap->ptrToTid, ptr); Map_Contains(allocMap->tidToPtr, x) && Map_At(allocMap->tidToPtr, x) == ptr))
}

type {:linear "tid"} Tid = int;

const memLo: int;
const memHi: int;
axiom 0 < memLo && memLo <= memHi;
function {:inline} memAddr(i: int) returns (bool) { memLo <= i && i < memHi }

var {:layer 0,1} isFree: [int]bool;
var {:layer 1,3} isFreeSet: Set int;
var {:layer 0,2} freeSpace: int;
var {:layer 2,3} allocMap: Bijection;

yield procedure {:layer 3} Malloc({:linear "tid"} tid: Tid)
preserves call YieldInvariant#1();
preserves call YieldInvariant#2(tid, false);
preserves call YieldInvariant#3(tid, false, memLo);
{
    var i: int;
    var spaceFound: bool;

    call DecrementFreeSpace#2(tid);
    i := memLo;
    while (i < memHi)
    invariant {:yields} true;
    invariant {:layer 1, 2} memLo <= i && i <= memHi;
    invariant {:layer 3} memAddr(i);
    invariant call YieldInvariant#1();
    invariant call YieldInvariant#2(tid, true);
    invariant call YieldInvariant#3(tid, true, i);
    {
        call spaceFound := AllocIfPtrFree#2(tid, i);
        if (spaceFound)
        {
            return;
        }
        i := i + 1;
    }
    call Unreachable(); // verification goal
}

yield procedure {:layer 3} Collect()
preserves call YieldInvariant#1();
{
    var ptr: int;

    while (*)
    invariant {:yields} true;
    invariant call YieldInvariant#1();
    {
        call ptr := Reclaim#2();
    }
}

action {:layer 2,3} Alloc(tid: Tid, ptr: int)
modifies allocMap;
{
    var tid': Tid;
    var ptr': int;
    assert Map_Contains(allocMap->tidToPtr, tid);
    if (Map_Contains(allocMap->ptrToTid, ptr)) {
        // swap
        tid' := Map_At(allocMap->ptrToTid, ptr);
        ptr' := Map_At(allocMap->tidToPtr, tid);
        allocMap := Bijection(Map_Swap(allocMap->tidToPtr, tid, tid'), Map_Swap(allocMap->ptrToTid, ptr, ptr'));
    }
    // alloc
    ptr' := Map_At(allocMap->tidToPtr, tid);
    allocMap := Bijection(Map_Remove(allocMap->tidToPtr, tid), Map_Remove(allocMap->ptrToTid, ptr'));
}

action {:layer 2,3} PreAlloc({:linear "tid"} tid: Tid, set: Set int)
modifies allocMap;
{
    var ptr: int;
    assert set != Set_Empty();
    ptr := Set_Choose(set);
    allocMap := Bijection(Map_Update(allocMap->tidToPtr, tid, ptr), Map_Update(allocMap->ptrToTid, ptr, tid));
}

atomic action {:layer 3} AtomicDecrementFreeSpace#2({:linear "tid"} tid: Tid)
modifies allocMap;
{
    var set: Set int;
    set := Set_Difference(isFreeSet, allocMap->ptrToTid->dom);
    assume set != Set_Empty();
    call PreAlloc(tid, set);
}
yield procedure {:layer 2} DecrementFreeSpace#2({:linear "tid"} tid: Tid)
refines AtomicDecrementFreeSpace#2;
preserves call YieldInvariant#1();
requires call YieldInvariant#2(tid, false);
ensures call YieldInvariant#2(tid, true);
{
    var set: Set int;
    call DecrementFreeSpace#0(tid);
    call PreAlloc(tid, Set_Difference(isFreeSet, allocMap->ptrToTid->dom));
}

atomic action {:layer 1,2} AtomicDecrementFreeSpace#0({:linear "tid"} tid: Tid)
modifies freeSpace;
{
    assume 0 < freeSpace;
    freeSpace := freeSpace - 1;
}
yield procedure {:layer 0} DecrementFreeSpace#0({:linear "tid"} tid: Tid);
refines AtomicDecrementFreeSpace#0;

atomic action {:layer 3} AtomicAllocIfPtrFree#2({:linear "tid"} tid: Tid, ptr: int) returns (spaceFound:bool)
modifies isFreeSet, allocMap;
{
    assert memAddr(ptr);
    spaceFound := Set_Contains(isFreeSet, ptr);
    if (spaceFound) {
        isFreeSet := Set_Remove(isFreeSet, ptr);
        call Alloc(tid, ptr);
    }
}
yield procedure {:layer 2} AllocIfPtrFree#2({:linear "tid"} tid: Tid, ptr: int) returns (spaceFound:bool)
refines AtomicAllocIfPtrFree#2;
preserves call YieldInvariant#1();
requires call YieldInvariant#2(tid, true);
ensures call YieldInvariant#2(tid, !spaceFound);
{
    call spaceFound := AllocIfPtrFree#1(tid, ptr);
    if (spaceFound) {
        call Alloc(tid, ptr);
    }
}

atomic action {:layer 2} AtomicAllocIfPtrFree#1({:linear "tid"} tid: Tid, ptr: int) returns (spaceFound:bool)
modifies isFreeSet;
{
    assert memAddr(ptr);
    spaceFound := Set_Contains(isFreeSet, ptr);
    if (spaceFound) {
        isFreeSet := Set_Remove(isFreeSet, ptr);
    }
}
yield procedure {:layer 1} AllocIfPtrFree#1({:linear "tid"} tid: Tid, ptr: int) returns (spaceFound:bool)
refines AtomicAllocIfPtrFree#1;
preserves call YieldInvariant#1();
{
    call spaceFound := AllocIfPtrFree#0(tid, ptr);
    if (spaceFound) {
        call IsFreeSetRemove(ptr);
    }
}

atomic action {:layer 1} AtomicAllocIfPtrFree#0({:linear "tid"} tid: Tid, ptr: int) returns (spaceFound:bool)
modifies isFree;
{
    assert memAddr(ptr);
    spaceFound := isFree[ptr];
    if (spaceFound) {
        isFree[ptr] := false;
    }
}
yield procedure {:layer 0} AllocIfPtrFree#0({:linear "tid"} tid: Tid, ptr: int) returns (spaceFound:bool);
refines AtomicAllocIfPtrFree#0;

atomic action {:layer 3} AtomicReclaim#2() returns (ptr: int)
modifies isFreeSet;
{
    assume memAddr(ptr) && !Set_Contains(isFreeSet, ptr);
    isFreeSet := Set_Add(isFreeSet, ptr);
}
yield procedure {:layer 2} Reclaim#2() returns (ptr: int)
refines AtomicReclaim#2;
preserves call YieldInvariant#1();
{
    call ptr := Reclaim#1();
}

action {:layer 1,2} IsFreeSetAdd(ptr: int)
modifies isFreeSet;
{
    isFreeSet := Set_Add(isFreeSet, ptr);
}

action {:layer 1,2} IsFreeSetRemove(ptr: int)
modifies isFreeSet;
{
    isFreeSet := Set_Remove(isFreeSet, ptr);
}

atomic action {:layer 2} AtomicReclaim#1() returns (ptr: int)
modifies freeSpace, isFreeSet;
{
    assume memAddr(ptr) && !Set_Contains(isFreeSet, ptr);
    freeSpace := freeSpace + 1;
    isFreeSet := Set_Add(isFreeSet, ptr);
}
yield procedure {:layer 1} Reclaim#1() returns (ptr: int)
refines AtomicReclaim#1;
preserves call YieldInvariant#1();
{
    call ptr := Reclaim#0();
    call IsFreeSetAdd(ptr);
}

atomic action {:layer 1} AtomicReclaim#0() returns (ptr: int)
modifies freeSpace, isFree;
{
    assume memAddr(ptr) && !isFree[ptr];
    freeSpace := freeSpace + 1;
    isFree[ptr] := true;
}
yield procedure {:layer 0} Reclaim#0() returns (ptr: int);
refines AtomicReclaim#0;

left action {:layer 1,3} AtomicUnreachable()
{
    assert false;
}
yield procedure {:layer 0} Unreachable();
refines AtomicUnreachable;

yield invariant {:layer 1} YieldInvariant#1();
invariant (forall y: int :: Set_Contains(isFreeSet, y) <==> memAddr(y) && isFree[y]);

yield invariant {:layer 2} YieldInvariant#2({:linear "tid"} tid: Tid, status: bool);
invariant Map_Contains(allocMap->tidToPtr, tid) == status;
invariant 0 <= freeSpace;
invariant freeSpace == Set_Size(Set_Difference(isFreeSet, allocMap->ptrToTid->dom));
invariant Set_IsSubset(allocMap->ptrToTid->dom, isFreeSet);
invariant BijectionInvariant(allocMap);

yield invariant {:layer 3} YieldInvariant#3({:linear "tid"} tid: Tid, status: bool, i: int);
invariant Map_Contains(allocMap->tidToPtr, tid) == status;
invariant Set_IsSubset(allocMap->ptrToTid->dom, isFreeSet);
invariant BijectionInvariant(allocMap);
invariant (forall y: int :: Set_Contains(isFreeSet, y) ==> memAddr(y));
invariant Map_Contains(allocMap->tidToPtr, tid) ==> i <= Map_At(allocMap->tidToPtr, tid);
