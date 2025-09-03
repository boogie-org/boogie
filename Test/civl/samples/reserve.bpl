// RUN: %parallel-boogie -lib:set_size "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*
This example models a memory allocator based on count of free cells (freeSpace) and an
array that keeps tracks of the allocation status of each cell (isFree). To allocate
a cell, freeSpace is decremented atomically, blocking to ensure that freeSpace does not
go below zero. If the decrement succeeds, then a scan of isFree is performed to find a
free cell. The goal of the verification is to prove that this scan will succeed. The
main challenge in the proof is to reason about cardinality of constructed sets.

At layer 1, isFree array is transformed into the finite set isFreeSet and the bijection
allocMap is introduced. The verification goal is discharged at layer 2 using cardinality
reasoning.
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
var {:layer 1,2} isFreeSet: Set int;
var {:layer 0,2} freeSpace: int;
var {:layer 1,2} allocMap: Bijection;

yield procedure {:layer 2} Malloc({:linear} tid: One Tid)
preserves call YieldInvariant#1();
preserves call YieldInvariant#2(tid, false, memLo);
{
    var i: int;
    var spaceFound: bool;

    call DecrementFreeSpace#1(tid);
    i := memLo;
    while (i < memHi)
    invariant {:yields} true;
    invariant {:layer 1} memLo <= i && i <= memHi;
    invariant {:layer 2} memAddr(i);
    invariant call YieldInvariant#1();
    invariant call YieldInvariant#2(tid, true, i);
    {
        call spaceFound := AllocIfPtrFree#1(tid, i);
        if (spaceFound)
        {
            return;
        }
        i := i + 1;
    }
    call Unreachable(); // verification goal
}

yield procedure {:layer 2} Collect()
preserves call YieldInvariant#1();
{
    var ptr: int;

    while (*)
    invariant {:yields} true;
    invariant call YieldInvariant#1();
    {
        call ptr := Reclaim#1();
    }
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

pure action PreAlloc({:linear} tid: One Tid, set: Set int, allocMap: Bijection) returns (allocMap': Bijection)
{
    var ptr: int;
    assert set != Set_Empty();
    ptr := Choice(set->val);
    allocMap' := Bijection(Map_Update(allocMap->tidToPtr, tid->val, ptr), Map_Update(allocMap->ptrToTid, ptr, tid->val));
}

atomic action {:layer 2} AtomicDecrementFreeSpace#1({:linear} tid: One Tid)
modifies freeSpace, allocMap;
{
    assert !Map_Contains(allocMap->tidToPtr, tid->val);
    call AtomicDecrementFreeSpace#0(tid);
    call allocMap := PreAlloc(tid, Set_Difference(isFreeSet, allocMap->ptrToTid->dom), allocMap);
}
yield procedure {:layer 1} DecrementFreeSpace#1({:linear} tid: One Tid)
refines AtomicDecrementFreeSpace#1;
preserves call YieldInvariant#1();
{
    call DecrementFreeSpace#0(tid);
    call {:layer 1} allocMap := PreAlloc(tid, Set_Difference(isFreeSet, allocMap->ptrToTid->dom), allocMap);
}

atomic action {:layer 1,2} AtomicDecrementFreeSpace#0({:linear} tid: One Tid)
modifies freeSpace;
{
    assume 0 < freeSpace;
    freeSpace := freeSpace - 1;
}
yield procedure {:layer 0} DecrementFreeSpace#0({:linear} tid: One Tid);
refines AtomicDecrementFreeSpace#0;

atomic action {:layer 2} AtomicAllocIfPtrFree#1({:linear} tid: One Tid, ptr: int) returns (spaceFound:bool)
modifies isFreeSet, allocMap;
{
    assert memAddr(ptr);
    assert Map_Contains(allocMap->tidToPtr, tid->val) && ptr <= Map_At(allocMap->tidToPtr, tid->val);
    spaceFound := Set_Contains(isFreeSet, ptr);
    if (spaceFound) {
        isFreeSet := Set_Remove(isFreeSet, ptr);
        call allocMap := Alloc(tid->val, ptr, allocMap);
    }
}
yield procedure {:layer 1} AllocIfPtrFree#1({:linear} tid: One Tid, ptr: int) returns (spaceFound:bool)
refines AtomicAllocIfPtrFree#1;
preserves call YieldInvariant#1();
{
    call spaceFound := AllocIfPtrFree#0(tid, ptr);
    if (spaceFound) {
        call {:layer 1} isFreeSet := Copy(Set_Remove(isFreeSet, ptr));
        call {:layer 1} allocMap := Alloc(tid->val, ptr, allocMap);
    }
}

atomic action {:layer 1} AtomicAllocIfPtrFree#0({:linear} tid: One Tid, ptr: int) returns (spaceFound:bool)
modifies isFree;
{
    assert memAddr(ptr);
    spaceFound := isFree[ptr];
    if (spaceFound) {
        isFree[ptr] := false;
    }
}
yield procedure {:layer 0} AllocIfPtrFree#0({:linear} tid: One Tid, ptr: int) returns (spaceFound:bool);
refines AtomicAllocIfPtrFree#0;

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
    call {:layer 1} isFreeSet := Copy(Set_Add(isFreeSet, ptr));
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

left action {:layer 1,2} AtomicUnreachable()
{
    assert false;
}
yield procedure {:layer 0} Unreachable();
refines AtomicUnreachable;

yield invariant {:layer 1} YieldInvariant#1();
preserves (forall y: int :: Set_Contains(isFreeSet, y) <==> memAddr(y) && isFree[y]);

yield invariant {:layer 2} YieldInvariant#2({:linear} tid: One Tid, status: bool, i: int);
preserves Map_Contains(allocMap->tidToPtr, tid->val) == status;
preserves Set_IsSubset(allocMap->ptrToTid->dom, isFreeSet);
preserves freeSpace + Set_Size(allocMap->ptrToTid->dom) == Set_Size(isFreeSet);
preserves BijectionInvariant(allocMap);
preserves (forall y: int :: Set_Contains(isFreeSet, y) ==> memAddr(y));
preserves Map_Contains(allocMap->tidToPtr, tid->val) ==> i <= Map_At(allocMap->tidToPtr, tid->val);
