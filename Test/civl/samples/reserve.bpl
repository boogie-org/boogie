// RUN: %parallel-boogie -lib:set_size "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*
This example models a memory allocator based on count of free cells (freeSpace) and an
array that keeps tracks of the allocation status of each cell (isFree). To allocate
a cell, freeSpace is decremented atomically, blocking to ensure that freeSpace does not
go below zero. If the decrement succeeds, then a scan of isFree is performed to find a
free cell. The goal of the verification is to prove that this scan will succeed. The
main challenge in the proof is to reason about cardinality of constructed sets.
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

type Tid = int;

const memLo: int;
const memHi: int;
axiom 0 < memLo && memLo <= memHi;
function {:inline} memAddr(i: int) returns (bool) { memLo <= i && i < memHi }

var {:layer 0,1} isFree: [int]bool;
var {:layer 0,1} freeSpace: int;
var {:layer 1,1} allocMap: Bijection;

yield procedure {:layer 1} Malloc({:linear} tid: One Tid)
preserves call YieldInvariant#1(tid, false, memLo);
{
    var i: int;
    var spaceFound: bool;

    call DecrementFreeSpace(tid);
    call {:layer 1} allocMap := PreAlloc(tid, Set_Difference(isFree, allocMap->ptrToTid->dom), allocMap);
    i := memLo;
    while (i < memHi)
    invariant {:yields} true;
    invariant {:layer 1} memAddr(i);
    invariant call YieldInvariant#1(tid, true, i);
    {
        call spaceFound := AllocIfPtrFree(tid, i);
        if (spaceFound)
        {
            call {:layer 1} allocMap := Alloc(tid->val, i, allocMap);
            return;
        }
        i := i + 1;
    }
    assert {:layer 1} false; // verification goal
}

yield procedure {:layer 1} Collect()
{
    var ptr: int;

    while (*)
    invariant {:yields} true;
    {
        call ptr := Reclaim();
    }
}

pure action PreAlloc({:linear} tid: One Tid, set: [int]bool, allocMap: Bijection) returns (allocMap': Bijection)
{
    var ptr: int;
    assert set != Set_Empty();
    ptr := Choice(set);
    allocMap' := Bijection(Map_Update(allocMap->tidToPtr, tid->val, ptr), Map_Update(allocMap->ptrToTid, ptr, tid->val));
}

pure action Alloc(tid: Tid, ptr: int, allocMap: Bijection) returns (allocMap': Bijection)
{
    var tid': Tid;
    var ptr': int;
    assert Map_Contains(allocMap->tidToPtr, tid);
    allocMap' := allocMap;
    if (Map_Contains(allocMap'->ptrToTid, ptr)) {
        // swap
        tid' := Map_At(allocMap'->ptrToTid, ptr);
        ptr' := Map_At(allocMap'->tidToPtr, tid);
        allocMap' := Bijection(Map_Swap(allocMap'->tidToPtr, tid, tid'), Map_Swap(allocMap'->ptrToTid, ptr, ptr'));
    }
    // alloc
    ptr' := Map_At(allocMap'->tidToPtr, tid);
    allocMap' := Bijection(Map_Remove(allocMap'->tidToPtr, tid), Map_Remove(allocMap'->ptrToTid, ptr'));
}

atomic action {:layer 1} AtomicDecrementFreeSpace({:linear} tid: One Tid)
modifies freeSpace;
{
    assume 0 < freeSpace;
    freeSpace := freeSpace - 1;
}
yield procedure {:layer 0} DecrementFreeSpace({:linear} tid: One Tid);
refines AtomicDecrementFreeSpace;

atomic action {:layer 1} AtomicAllocIfPtrFree({:linear} tid: One Tid, ptr: int) returns (spaceFound:bool)
{
    assert memAddr(ptr);
    spaceFound := isFree[ptr];
    if (spaceFound) {
        isFree[ptr] := false;
    }
}
yield procedure {:layer 0} AllocIfPtrFree({:linear} tid: One Tid, ptr: int) returns (spaceFound:bool);
refines AtomicAllocIfPtrFree;

atomic action {:layer 1} AtomicReclaim() returns (ptr: int)
{
    assume memAddr(ptr) && !isFree[ptr];
    freeSpace := freeSpace + 1;
    isFree[ptr] := true;
}
yield procedure {:layer 0} Reclaim() returns (ptr: int);
refines AtomicReclaim;

yield invariant {:layer 1} YieldInvariant#1({:linear} tid: One Tid, status: bool, i: int);
preserves Map_Contains(allocMap->tidToPtr, tid->val) == status;
preserves Set_IsSubset(allocMap->ptrToTid->dom, isFree);
preserves freeSpace + Set_Size(allocMap->ptrToTid->dom) == Set_Size(isFree);
preserves BijectionInvariant(allocMap);
preserves (forall y: int :: Set_Contains(isFree, y) ==> memAddr(y));
preserves Map_Contains(allocMap->tidToPtr, tid->val) ==> i <= Map_At(allocMap->tidToPtr, tid->val);
