// RUN: %parallel-boogie /vcsSplitOnEveryAssert "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*
This example models a memory allocator based on count of free cells (freeSpace) and an
array that keeps tracks of the allocation status of each cell (isFree). To allocate
a cell, freeSpace is decremented atomically, blocking to ensure that freeSpace does not
go below zero. If the decrement succeeds, then a scan of isFree is performed to find a
free cell. The goal of the verification is to prove that this scan will succeed. The
main challenge in the proof is to reason about cardinality of constructed sets.
*/

type {:linear "tid"} Tid = int;

const memLo: int;
const memHi: int;
axiom 0 < memLo && memLo <= memHi;
function {:inline} memAddr(i: int) returns (bool) { memLo <= i && i < memHi }

datatype Bijection {
  Bijection(domain: [Tid]bool, range: [int]bool, tidToPtr: [Tid]int, ptrToTid: [int]Tid)
}

var {:layer 0,1} isFree: [int]bool;
var {:layer 0,1} freeSpace: int;
var {:layer 0,1} allocMap: Bijection;

function {:inline} BijectionInvariant(allocMap: Bijection): bool {
    (forall {:pool "A"} tid: Tid :: {:add_to_pool "A", tid} {:add_to_pool "B", allocMap->tidToPtr[tid]}
        allocMap->domain[tid] ==>
            allocMap->range[allocMap->tidToPtr[tid]] &&
            allocMap->ptrToTid[allocMap->tidToPtr[tid]] == tid)
    &&
    (forall {:pool "B"} ptr: int :: {:add_to_pool "B", ptr} {:add_to_pool "A", allocMap->ptrToTid[ptr]}
        allocMap->range[ptr] ==>
            allocMap->domain[allocMap->ptrToTid[ptr]] &&
            allocMap->tidToPtr[allocMap->ptrToTid[ptr]] == ptr)
}

yield invariant {:layer 1} YieldInvariant();
invariant 0 <= freeSpace;
invariant BijectionInvariant(allocMap);
invariant (forall {:pool "B"} y: int :: {:add_to_pool "B", y} isFree[y] ==> memAddr(y));
invariant MapDiff(allocMap->range, isFree) == MapConst(false);
invariant freeSpace == Size(MapDiff(isFree, allocMap->range));

yield invariant {:layer 1} YieldAllocMap({:linear "tid"} tid: Tid, status: bool, i: int);
invariant allocMap->domain[tid] == status;
invariant allocMap->domain[tid] ==> i <= allocMap->tidToPtr[tid];

function Size<T>([T]bool) returns (int);

pure procedure SizeLemma1<T>(X: [T]bool, x: T);
ensures Size(X[x := false]) + 1 == Size(X[x := true]);

pure procedure SizeLemma2<T>(X: [T]bool, Y: [T]bool);
requires MapDiff(X, Y) == MapConst(false);
ensures Size(Y) == Size(X) + Size(MapDiff(Y, X));

yield procedure {:layer 0} DecrementFreeSpace({:linear "tid"} tid: Tid);
refines atomic_DecrementFreeSpace;

atomic action {:layer 1} atomic_DecrementFreeSpace({:linear "tid"} tid: Tid)
modifies freeSpace, allocMap;
{
    var ptr: int;
    assume 0 < freeSpace;
    assert !allocMap->domain[tid];
    assert freeSpace == Size(MapDiff(isFree, allocMap->range));
    assume MapDiff(isFree, allocMap->range)[ptr];
    freeSpace := freeSpace - 1;
    call allocMap := Reserve(allocMap, tid, ptr);
}

atomic action Reserve(allocMap: Bijection, tid: Tid, ptr: int) returns (allocMap': Bijection) {
    assert !allocMap->domain[tid];
    assert !allocMap->range[ptr];
    assert memAddr(ptr);
    allocMap' := Bijection(
                    allocMap->domain[tid := true],
                    allocMap->range[ptr := true],
                    allocMap->tidToPtr[tid := ptr],
                    allocMap->ptrToTid[ptr := tid]);
}

yield procedure {:layer 0} AllocIfPtrFree({:linear "tid"} tid: Tid, ptr: int) returns (spaceFound:bool);
refines atomic_AllocIfPtrFree;

atomic action {:layer 1} atomic_AllocIfPtrFree({:linear "tid"} tid: Tid, ptr: int) returns (spaceFound:bool)
modifies isFree, allocMap;
{
    var tid': Tid;
    var ptr': int;
    assert memAddr(ptr);
    assert isFree[ptr] || memAddr(ptr + 1);
    assert allocMap->domain[tid];
    spaceFound := isFree[ptr];
    if (spaceFound) {
        isFree[ptr] := false;
        assume {:add_to_pool "A", tid} {:add_to_pool "B", ptr} true;
        call allocMap := Alloc(allocMap, tid, ptr);
    }
}

atomic action Alloc(allocMap: Bijection, tid: Tid, ptr: int) returns (allocMap': Bijection) {
    var tid': Tid;
    var ptr': int;
    assert allocMap->domain[tid];
    allocMap' := allocMap;
    if (allocMap'->range[ptr]) {
        // swap
        tid' := allocMap'->ptrToTid[ptr];
        ptr' := allocMap'->tidToPtr[tid];
        assume {:add_to_pool "A", tid'} {:add_to_pool "B", ptr'} true;
        allocMap' := Bijection(
                        allocMap'->domain,
                        allocMap'->range,
                        allocMap'->tidToPtr[tid := ptr][tid' := ptr'],
                        allocMap'->ptrToTid[ptr := tid][ptr' := tid']);
    }
    // alloc
    ptr' := allocMap'->tidToPtr[tid];
    assume {:add_to_pool "B", ptr'} true;
    allocMap' := Bijection(
                    allocMap'->domain[tid := false],
                    allocMap'->range[ptr' := false],
                    allocMap'->tidToPtr,
                    allocMap'->ptrToTid);
}

yield procedure {:layer 0} Reclaim() returns (ptr: int);
refines atomic_Reclaim;

atomic action {:layer 1} atomic_Reclaim() returns (ptr: int)
modifies freeSpace, isFree;
{
    assume memAddr(ptr) && !isFree[ptr];
    freeSpace := freeSpace + 1;
    isFree[ptr] := true;
}

yield procedure {:layer 1} Malloc({:linear "tid"} tid: Tid)
requires call YieldAllocMap(tid, false, memLo);
preserves call YieldInvariant();
{
    var i: int;
    var spaceFound: bool;

    call DecrementFreeSpace(tid);
    i := memLo;
    call {:layer 1} SizeLemma1(MapDiff(isFree, allocMap->range), allocMap->tidToPtr[tid]);
    while (i < memHi)
    invariant {:layer 1} memAddr(i);
    invariant {:yields} true;
    invariant call YieldInvariant();
    invariant call YieldAllocMap(tid, true, i);
    {
        call {:layer 1} SizeLemma1(isFree, i);
        call {:layer 1} SizeLemma1(allocMap->range, i);
        call {:layer 1} SizeLemma1(allocMap->range, allocMap->tidToPtr[tid]);
        call {:layer 1} SizeLemma2(allocMap->range, isFree);
        call spaceFound := AllocIfPtrFree(tid, i);
        if (spaceFound)
        {
            call {:layer 1} SizeLemma2(allocMap->range, isFree);
            return;
        }
        i := i + 1;
    }
    assert {:layer 1} false;
}

yield procedure {:layer 1} Collect()
preserves call YieldInvariant();
{
    var ptr: int;

    while (*)
    invariant {:yields} true;
    invariant call YieldInvariant();
    {
        call ptr := Reclaim();
        call {:layer 1} SizeLemma1(MapDiff(isFree, allocMap->range), ptr);
    }
}
