// RUN: %parallel-boogie "%s" > "%t"
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

type {:datatype} Bijection;
function {:constructor} Bijection(domain: [Tid]bool, range: [int]bool, tidToPtr: [Tid]int, ptrToTid: [int]Tid): Bijection;

var {:layer 0,1} isFree: [int]bool;
var {:layer 0,1} freeSpace: int;
var {:layer 0,1} allocMap: Bijection;

function {:inline} BijectionInvariant(allocMap: Bijection): bool {
    (forall tid: Tid ::
        domain#Bijection(allocMap)[tid] ==>
            range#Bijection(allocMap)[tidToPtr#Bijection(allocMap)[tid]] &&
            ptrToTid#Bijection(allocMap)[tidToPtr#Bijection(allocMap)[tid]] == tid)
    &&
    (forall ptr: int ::
        range#Bijection(allocMap)[ptr] ==>
            domain#Bijection(allocMap)[ptrToTid#Bijection(allocMap)[ptr]] &&
            tidToPtr#Bijection(allocMap)[ptrToTid#Bijection(allocMap)[ptr]] == ptr)
}

procedure {:yield_invariant} {:layer 1} YieldInvariant();
requires 0 <= freeSpace;
requires BijectionInvariant(allocMap);
requires (forall y: int :: isFree[y] ==> memAddr(y));
requires MapDiff(range#Bijection(allocMap), isFree) == MapConst(false);
requires freeSpace == Size(MapDiff(isFree, range#Bijection(allocMap)));

function Size<T>([T]bool) returns (int);

procedure {:lemma} SizeLemma1<T>(X: [T]bool, x: T);
ensures Size(X[x := false]) + 1 == Size(X[x := true]);

procedure {:lemma} SizeLemma2<T>(X: [T]bool, Y: [T]bool);
requires MapDiff(X, Y) == MapConst(false);
ensures Size(Y) == Size(X) + Size(MapDiff(Y, X));

procedure {:yields} {:layer 0} {:refines "atomic_DecrementFreeSpace"} DecrementFreeSpace({:linear "tid"} tid: Tid);

procedure {:atomic} {:layer 1} atomic_DecrementFreeSpace({:linear "tid"} tid: Tid)
modifies freeSpace, allocMap;
{
    var ptr: int;
    assume 0 < freeSpace;
    assert !domain#Bijection(allocMap)[tid];
    assert freeSpace == Size(MapDiff(isFree, range#Bijection(allocMap)));
    assume MapDiff(isFree, range#Bijection(allocMap))[ptr];
    freeSpace := freeSpace - 1;
    call allocMap := Reserve(allocMap, tid, ptr);
}

procedure {:atomic} Reserve(allocMap: Bijection, tid: Tid, ptr: int) returns (allocMap': Bijection) {
    assert !domain#Bijection(allocMap)[tid];
    assert !range#Bijection(allocMap)[ptr];
    assert memAddr(ptr);
    allocMap' := Bijection(
                    domain#Bijection(allocMap)[tid := true],
                    range#Bijection(allocMap)[ptr := true],
                    tidToPtr#Bijection(allocMap)[tid := ptr],
                    ptrToTid#Bijection(allocMap)[ptr := tid]);
}

procedure {:yields} {:layer 0} {:refines "atomic_AllocIfPtrFree"} AllocIfPtrFree({:linear "tid"} tid: Tid, ptr: int) returns (spaceFound:bool);

procedure {:atomic} {:layer 1} atomic_AllocIfPtrFree({:linear "tid"} tid: Tid, ptr: int) returns (spaceFound:bool)
modifies isFree, allocMap;
{
    var tid': Tid;
    var ptr': int;
    assert memAddr(ptr);
    assert isFree[ptr] || memAddr(ptr + 1);
    assert domain#Bijection(allocMap)[tid];
    spaceFound := isFree[ptr];
    if (spaceFound) {
        isFree[ptr] := false;
        call allocMap := Alloc(allocMap, tid, ptr);
    }
}

procedure {:atomic} Alloc(allocMap: Bijection, tid: Tid, ptr: int) returns (allocMap': Bijection) {
    var tid': Tid;
    var ptr': int;
    assert domain#Bijection(allocMap)[tid];
    allocMap' := allocMap;
    if (range#Bijection(allocMap')[ptr]) {
        // swap
        tid' := ptrToTid#Bijection(allocMap')[ptr];
        ptr' := tidToPtr#Bijection(allocMap')[tid];
        allocMap' := Bijection(
                        domain#Bijection(allocMap'),
                        range#Bijection(allocMap'),
                        tidToPtr#Bijection(allocMap')[tid := ptr][tid' := ptr'],
                        ptrToTid#Bijection(allocMap')[ptr := tid][ptr' := tid']);
    }
    // alloc
    ptr' := tidToPtr#Bijection(allocMap')[tid];
    allocMap' := Bijection(
                    domain#Bijection(allocMap')[tid := false],
                    range#Bijection(allocMap')[ptr' := false],
                    tidToPtr#Bijection(allocMap'),
                    ptrToTid#Bijection(allocMap'));
}

procedure {:yields} {:layer 0} {:refines "atomic_Reclaim"} Reclaim() returns (ptr: int);

procedure {:atomic} {:layer 1} atomic_Reclaim() returns (ptr: int)
modifies freeSpace, isFree;
{
    assume memAddr(ptr) && !isFree[ptr];
    freeSpace := freeSpace + 1;
    isFree[ptr] := true;
}

procedure {:yields} {:layer 1}
{:yield_requires "YieldInvariant"}
{:yield_ensures "YieldInvariant"}
Malloc({:linear "tid"} tid: Tid)
requires {:layer 1} !domain#Bijection(allocMap)[tid];
{
    var i: int;
    var spaceFound: bool;

    call DecrementFreeSpace(tid);
    i := memLo;
    call {:layer 1} SizeLemma1(MapDiff(isFree, range#Bijection(allocMap)), tidToPtr#Bijection(allocMap)[tid]);
    while (i < memHi)
    invariant {:yields} {:layer 1} memAddr(i) && domain#Bijection(allocMap)[tid] && i <= tidToPtr#Bijection(allocMap)[tid];
    invariant {:yields} {:layer 1} {:yield_loop "YieldInvariant"} true;
    {
        call {:layer 1} SizeLemma1(isFree, i);
        call {:layer 1} SizeLemma1(range#Bijection(allocMap), i);
        call {:layer 1} SizeLemma1(range#Bijection(allocMap), tidToPtr#Bijection(allocMap)[tid]);
        call {:layer 1} SizeLemma2(range#Bijection(allocMap), isFree);
        call spaceFound := AllocIfPtrFree(tid, i);
        if (spaceFound)
        {
            call {:layer 1} SizeLemma2(range#Bijection(allocMap), isFree);
            return;
        }
        i := i + 1;
    }
    assert {:layer 1} false;
}

procedure {:yields} {:layer 1}
{:yield_requires "YieldInvariant"}
{:yield_ensures "YieldInvariant"}
Collect()
{
    var ptr: int;

    while (*)
    invariant {:yields} {:layer 1} {:yield_loop "YieldInvariant"} true;
    {
        call ptr := Reclaim();
        call {:layer 1} SizeLemma1(MapDiff(isFree, range#Bijection(allocMap)), ptr);
    }
}
