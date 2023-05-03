//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "tid"} X = int;
function {:inline} Subset(X: [X]bool, Y: [X]bool) : (bool)
{
    MapOr(MapNot(X), Y) == MapConst(true)
}

// Tid(i, left, right) represents a linear thread id for thread number i, where i > 0.
// Thread ids can be split into left and right fractions:
//   - For a whole thread id, both the left and right fields are true.
//   - For a fraction, either the left or right field is true.
// In other words, Tid(i, true, true) can be be split into Tid(i, true, false), Tid(i, false, true).
datatype Tid { Tid(i:int, left:bool, right:bool) }

function {:inline} {:linear "tid"} TidCollector(x: Tid) : [X]bool
{
    MapConst(false)[-x->i := x->left][x->i := x->right]
}

const numMutators: int;
axiom 0 < numMutators;
const GcTid: Tid;
axiom numMutators < GcTid->i && GcTid->left && GcTid->right;

function mutatorId(i: int) : bool { 1 <= i && i <= numMutators }
function mutatorTid(tid: Tid) : bool { mutatorId(tid->i) }
function mutatorTidLeft(tid: Tid) : bool { mutatorTid(tid) && tid->left }
function mutatorTidRight(tid: Tid) : bool { mutatorTid(tid) && tid->right }
function mutatorTidWhole(tid: Tid) : bool { mutatorTid(tid) && tid->left && tid->right }
function gcAndMutatorTids(tid: Tid, mutatorTids: [int]bool) : bool
{
    tid == GcTid && (forall i:int :: mutatorId(i) ==> mutatorTids[i] && mutatorTids[-i])
}

function Size([int]bool) returns (int);
const Mutators: [int]bool;
axiom Size(Mutators) == numMutators;
axiom Size(MapConst(false)) == 0;
axiom (forall X, Y: [int]bool :: Subset(X, Y) ==> Size(X) < Size(Y) || X == Y);
axiom (forall X: [int]bool, x: int ::{Size(X[x := false]), Size(X[x := true])} Size(X[x := false]) + 1 == Size(X[x := true]));
axiom (forall x: int :: Mutators[x] <==> 1 <= x && x <= numMutators);
function {:inline} RootScanBarrierInv(Set:[int]bool, rootScanBarrier: int) : bool
{
    Size(Set) + rootScanBarrier == numMutators &&
    Subset(Set, Mutators)
}

type idx = int;
type fld = int;
datatype obj { Nil(), Obj(id:int), Int(i:int) }

function {:inline} IDLE():int { 0 }
function {:inline} MARK():int { 1 }
function {:inline} SWEEP():int { 2 }
function {:inline} IdlePhase(i:int):bool { i <= 0 }
function {:inline} MarkPhase(i:int):bool { i == 1 }
function {:inline} SweepPhase(i:int):bool { i >= 2 }

function {:inline} UNALLOC():int { 0 }
function {:inline} WHITE():int { 1 }
function {:inline} GRAY():int { 2 }
function {:inline} BLACK():int { 3 }
function {:inline} Unalloc(i:int) returns(bool) { i <= 0 }
function {:inline} White(i:int) returns(bool) { i == 1 }
function {:inline} Gray(i:int) returns(bool) { i == 2 }
function {:inline} Black(i:int) returns(bool) { i >= 3 }

// Top layer
var {:layer 99,101} rootAbs:[idx]obj;
var {:layer 0,101} allocSet:[obj]bool;
var {:layer 99,101} memAbs:[obj][fld]obj;

// Next layer
var {:layer 0,100} root:[idx]int;
var {:layer 0,100} mem:[int][fld]int;
var {:layer 95,100} toAbs:[int]obj; // ghost variable
var {:layer 0,100} Color:[int]int;
var {:layer 0,100} collectorPhase: int;
var {:layer 0,100} mutatorPhase:[X]int;
var {:layer 0,100} sweepPtr: int;

// Next layer
var {:layer 0,99} rootScanOn: bool;
var {:layer 0,99} rootScanBarrier: int;
var {:linear "tid"} {:layer 0,99} mutatorsInRootScanBarrier:[int]bool; // ghost variable
var {:layer 0,98} MarkStack:[int]int;
var {:layer 0,98} MarkStackPtr:int;

// Next layer
// Lock is used during allocation, GC.  To ensure good performance, it is not used for mutator reads and writes.
var {:layer 0,96} lock:int; // 0 if unheld; thread number of holder if held

function tidHasLock(tid:Tid, lock:int):bool { (tid == GcTid || mutatorTid(tid)) && lock == tid->i && tid->left }

const memLo: int;
const memHi: int;
axiom 0 < memLo && memLo <= memHi;
function {:inline} memAddr(i:int) returns (bool) { memLo <= i && i < memHi }

function memAddrAbs(i:obj) returns (bool);

const numFields: int;
axiom 0 <= numFields;
function {:inline} fieldAddr(i:int) returns (bool) { 0 <= i && i < numFields }

const numRoots: int;
axiom 0 <= numRoots;
function {:inline} rootAddr(i:int) returns (bool) { 0 <= i && i < numRoots }

const nil: obj;
axiom nil == Nil();
axiom memAddrAbs(Nil());
axiom (forall i:int :: memAddrAbs(Obj(i)));
axiom (forall i:int :: !memAddrAbs(Int(i)));

function owner(x: idx): X;
function tidOwns(tid:Tid, x:idx):bool { owner(x) == tid->i }

function {:inline} Iso(root:[idx]int, rootAbs:[idx]obj, mem:[int][fld]int, memAbs:[obj][fld]obj, Color:[int]int, toAbs:[int]obj, allocSet:[obj]bool) returns (bool)
{
    (forall x: int :: memAddr(x) <==> memAddrAbs(toAbs[x])) &&
    (forall x: int, y: int :: toAbs[x] == toAbs[y] ==> x == y || (memAddr(x) && toAbs[x] == nil) || (memAddr(y) && toAbs[y] == nil)) &&
    (forall x: idx :: rootAddr(x) ==> toAbs[root[x]] == rootAbs[x]) &&
    (forall x: int, f: fld :: memAddr(x) && toAbs[x] != nil && fieldAddr(f) ==> toAbs[mem[x][f]] == memAbs[toAbs[x]][f]) &&
    (forall x: int :: memAddr(x) && toAbs[x] != nil ==> allocSet[toAbs[x]]) &&
    (forall x: idx :: rootAddr(x) && memAddr(root[x]) ==> toAbs[root[x]] != nil) &&
    (forall x: int, f: fld :: memAddr(x) && toAbs[x] != nil && fieldAddr(f) && memAddr(mem[x][f]) ==> toAbs[mem[x][f]] != nil) &&
    (forall x: int, f: fld :: memAddr(x) && Unalloc(Color[x]) ==> toAbs[x] == nil)
}

function {:inline false} MST(i:int) returns (bool) { true }

function {:inline} MsWellFormed(MarkStack:[int]int, MarkStackPtr:int, Color:[int]int, nodePeeked:int) returns (bool)
{
    (forall i:int :: {MST(i)} MST(i) ==> (0 <= i && i < MarkStackPtr) ==> (memAddr(MarkStack[i]) && Gray(Color[MarkStack[i]]))) &&
    (nodePeeked != 0 ==> memAddr(nodePeeked) && Gray(Color[nodePeeked])) &&
    (forall i:int :: (memAddr(i) && Gray(Color[i])) ==>  (exists j:int :: {MST(j)} MST(j) && 0 <= j && j < MarkStackPtr && MarkStack[j] == i) || nodePeeked == i) &&
    (forall i:int :: {MST(i)} MST(i) ==> (0 <= i && i < MarkStackPtr) ==> (forall j:int :: {MST(j)} MST(j) ==> (0 <= j && j < MarkStackPtr && i != j) ==> MarkStack[i] != MarkStack[j])) &&
    (forall i:int :: {MST(i)} MST(i) ==> (0 <= i && i < MarkStackPtr) ==> MarkStack[i] != nodePeeked) &&
    (0 <= MarkStackPtr)
}

function {:inline} PhaseConsistent(collectorPhase: int, mutatorPhase: [int]int) returns (bool)
{
    (forall i: int :: mutatorId(i) ==> mutatorPhase[i] == collectorPhase)
}

function {:inline} MarkInv(root:[idx]int, rootAbs:[idx]obj, mem:[int][fld]int, memAbs:[obj][fld]obj, Color:[int]int, toAbs:[int]obj, allocSet:[obj]bool) returns (bool)
{
    Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet) &&
    (forall x: int :: memAddr(x) ==> (toAbs[x] == nil <==> Unalloc(Color[x]))) &&
    (forall x: int, f: fld :: memAddr(x) && Black(Color[x]) && fieldAddr(f) && memAddr(mem[x][f]) ==> Gray(Color[mem[x][f]]) || Black(Color[mem[x][f]]))
}

function {:inline} SweepInv(root:[idx]int, rootAbs:[idx]obj, mem:[int][fld]int, memAbs:[obj][fld]obj, Color:[int]int, toAbs:[int]obj, allocSet:[obj]bool) returns (bool)
{
    Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet) &&
    (forall x: int :: memAddr(x) ==> (toAbs[x] == nil <==> Unalloc(Color[x]))) &&
    (forall x: int :: memAddr(x) ==> !Gray(Color[x])) &&
    (forall x: int, f: fld :: memAddr(x) && Black(Color[x]) && fieldAddr(f) && memAddr(mem[x][f]) ==> Black(Color[mem[x][f]]))
}

function {:inline} SweepInvInit(root:[idx]int, rootAbs:[idx]obj, mem:[int][fld]int, memAbs:[obj][fld]obj, Color:[int]int, toAbs:[int]obj, allocSet:[obj]bool) returns (bool)
{
    Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet) &&
    (forall x: int :: memAddr(x) ==> (toAbs[x] != nil <==> Black(Color[x]))) &&
    (forall x: int :: memAddr(x) ==> !Gray(Color[x])) &&
    (forall x: int, f: fld :: memAddr(x) && Black(Color[x]) && fieldAddr(f) && memAddr(mem[x][f]) ==> Black(Color[mem[x][f]]))
}

//////////////////////////////////////////////////////////////////////////////
// Layer 100
//////////////////////////////////////////////////////////////////////////////

yield invariant {:layer 100} Yield_WriteField({:linear "tid"} tid:Tid, x: idx, y: idx);
invariant mutatorTidWhole(tid) && tidOwns(tid, x) && tidOwns(tid, y);
invariant memAddr(root[y]) && MarkPhase(mutatorPhase[tid->i]) ==> Gray(Color[root[y]]) || Black(Color[root[y]]);

yield invariant {:layer 100} Yield_Iso();
invariant Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);

yield invariant {:layer 100} Yield_GarbageCollect_100({:linear "tid"} tid:Tid);
invariant tid == GcTid;
invariant (forall x: int :: memAddr(x) ==> (toAbs[x] == nil <==> Unalloc(Color[x])));
invariant sweepPtr == memHi ==> (forall x: int :: memAddr(x) ==> !Black(Color[x]));
invariant sweepPtr == memLo ==>
            (forall x: int :: memAddr(x) ==> !Gray(Color[x])) &&
            (forall i: int :: rootAddr(i) && memAddr(root[i]) ==> Black(Color[root[i]])) &&
            (forall x: int, f: fld :: memAddr(x) && Black(Color[x]) && fieldAddr(f) && memAddr(mem[x][f]) ==> Black(Color[mem[x][f]]));

yield invariant {:layer 100} Yield_CollectorPhase_100({:linear "tid"} tid:Tid, tick_collectorPhase: int);
invariant tid == GcTid;
invariant tick_collectorPhase == collectorPhase;

yield invariant {:layer 100} Yield_SweepPtr_100({:linear "tid"} tid:Tid, tick_sweepPtr: int);
invariant tid == GcTid;
invariant tick_sweepPtr == sweepPtr;

yield invariant {:layer 100} YieldMarkBegin({:linear "tid"} tid:Tid, tick_Color: [int]int);
invariant tid == GcTid;
invariant MarkPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase) && sweepPtr == memHi;
invariant (forall x: int :: memAddr(x) ==> (toAbs[x] == nil <==> Unalloc(Color[x])));
invariant (forall x: int :: memAddr(x) ==> !Black(Color[x]));
invariant (forall x: int :: memAddr(x) && !Unalloc(tick_Color[x]) ==> !Unalloc(Color[x]));
invariant (forall x: int :: memAddr(x) && !Unalloc(tick_Color[x]) && !White(tick_Color[x]) ==> !White(Color[x]));

yield invariant {:layer 100} YieldMark({:linear "tid"} tid:Tid, tick_Color: [int]int);
invariant tid == GcTid;
invariant MarkPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase) && sweepPtr == memLo;
invariant MarkInv(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
invariant (forall x: int :: memAddr(x) && !Unalloc(tick_Color[x]) ==> !Unalloc(Color[x]));
invariant (forall x: int :: memAddr(x) && !Unalloc(tick_Color[x]) && !White(tick_Color[x]) ==> !White(Color[x]));

yield invariant {:layer 100} YieldMarkEnd({:linear "tid"} tid:Tid);
invariant tid == GcTid;
invariant MarkPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase) && sweepPtr == memLo;
invariant MarkInv(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
invariant (forall x: int :: memAddr(x) ==> !Gray(Color[x]));
invariant (forall i: int :: rootAddr(i) && memAddr(root[i]) ==> Black(Color[root[i]]));

yield invariant {:layer 100} Yield_MarkInnerLoopFieldIter({:linear "tid"} tid:Tid, fldIter: int, nodeProcessed: int);
invariant tid == GcTid;
invariant 0 <= fldIter && fldIter <= numFields;
invariant MarkPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase) && sweepPtr == memLo;
invariant MarkInv(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
invariant !Unalloc(Color[nodeProcessed]);
invariant (forall x: int :: 0 <= x && x < fldIter && memAddr(mem[nodeProcessed][x]) ==> !Unalloc(Color[mem[nodeProcessed][x]]) && !White(Color[mem[nodeProcessed][x]]));

yield invariant {:layer 100} YieldSweepBegin({:linear "tid"} tid:Tid, isInit: bool, tick_Color: [int]int);
invariant tid == GcTid;
invariant SweepPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase);
invariant sweepPtr == memLo;
invariant !isInit ==> SweepInv(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
invariant isInit ==> SweepInvInit(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
invariant (forall i: int :: rootAddr(i) && memAddr(root[i]) ==> Black(Color[root[i]]));
invariant (forall x: int :: memAddr(x) && !Unalloc(tick_Color[x]) ==> tick_Color[x] == Color[x]);

yield invariant {:layer 100} YieldSweepEnd({:linear "tid"} tid:Tid);
invariant tid == GcTid;
invariant SweepPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase);
invariant sweepPtr == memHi;
invariant SweepInv(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
invariant (forall x: int :: memAddr(x) ==> !Black(Color[x]));

yield invariant {:layer 100} Yield_Initialize_100({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool);
invariant gcAndMutatorTids(tid, mutatorTids);
invariant (forall x: idx :: rootAddr(x) ==> rootAbs[x] == Int(0));

yield procedure {:layer 100}
Initialize({:linear_in "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool)
requires {:layer 97,98,99} gcAndMutatorTids(tid, mutatorTids);
requires call Yield_Initialize_100(tid, mutatorTids);
requires call Yield_InitVars99(mutatorTids, MapConst(false) : [int]bool, old(rootScanBarrier));
ensures call Yield_Iso();
ensures call Yield_RootScanBarrierInv();
ensures call Yield_InitVars99(mutatorTids, MapConst(false) : [int]bool, numMutators);
{
    call InitVars99(tid, mutatorTids);
    call InitVars100(tid, mutatorTids);
    async call GarbageCollect(tid);
}

>-< action {:layer 101} AtomicAlloc({:linear "tid"} tid:Tid, y:idx)
modifies allocSet, rootAbs, memAbs;
{
    var o: obj;
    assert mutatorTidWhole(tid) && rootAddr(y) && tidOwns(tid, y);
    assume (memAddrAbs(o) && !allocSet[o]);
    allocSet[o] := true;
    rootAbs[y] := o;
    memAbs[o] := (lambda z: int :: if (fieldAddr(z)) then o else memAbs[o][z]);
}

yield procedure {:layer 100}
Alloc({:linear "tid"} tid:Tid, y:idx)
refines AtomicAlloc;
requires {:layer 95,96,99,100} mutatorTidWhole(tid);
preserves call Yield_Iso();
requires call Yield_RootScanBarrierEnter(tid);
requires call Yield_RootScanBarrierInv();
{
    var ptr: int;
    var absPtr: obj;

    call TestRootScanBarrier(tid);
    call Yield_Iso();
    call UpdateMutatorPhase(tid);
    call Yield_Iso();
    call ptr, absPtr := AllocRaw(tid, y);
}

>-< action {:layer 101} AtomicWriteField({:linear "tid"} tid:Tid, x: idx, f: fld, y: idx) // x.f = y
modifies memAbs;
{ assert mutatorTidWhole(tid) && rootAddr(x) && tidOwns(tid, x) && fieldAddr(f) && rootAddr(y) && tidOwns(tid, y) && memAddrAbs(rootAbs[x]); memAbs[rootAbs[x]][f] := rootAbs[y]; }

yield procedure {:layer 100}
WriteField({:linear "tid"} tid:Tid, x: idx, f: fld, y: idx)
refines AtomicWriteField;
requires {:layer 98, 100} mutatorTidWhole(tid);
preserves call Yield_Iso();
{
    call WriteBarrier(tid, y);
    par Yield_Iso() | Yield_WriteField(tid, x, y);
    call WriteFieldRaw(tid, x, f, y);
}

>-< action {:layer 101} AtomicReadField({:linear "tid"} tid:Tid, x: idx, f: fld, y: idx) // y = x.f
modifies rootAbs;
{ assert mutatorTidWhole(tid) && rootAddr(x) && tidOwns(tid, x) && fieldAddr(f) && rootAddr(y) && tidOwns(tid, y) && memAddrAbs(rootAbs[x]); rootAbs[y] := memAbs[rootAbs[x]][f]; }

yield procedure {:layer 100}
ReadField({:linear "tid"} tid:Tid, x: idx, f: fld, y: idx)
refines AtomicReadField;
preserves call Yield_Iso();
{
    call ReadFieldRaw(tid, x, f, y);
}

>-< action {:layer 101} AtomicEq({:linear "tid"} tid:Tid, x: idx, y:idx) returns (isEqual:bool)
{ assert mutatorTidWhole(tid) && rootAddr(x) && tidOwns(tid, x) && rootAddr(y) && tidOwns(tid, y); isEqual := rootAbs[x] == rootAbs[y]; }

yield procedure {:layer 100}
Eq({:linear "tid"} tid:Tid, x: idx, y:idx) returns (isEqual:bool)
refines AtomicEq;
preserves call Yield_Iso();
{
    call isEqual := EqRaw(tid, x, y);
}

yield procedure {:layer 100}
GarbageCollect({:linear "tid"} tid:Tid)
requires {:layer 97,98,99,100} tid == GcTid;
requires call Yield_Iso();
requires call Yield_MsWellFormed(tid, 0);
requires call Yield_RootScanBarrierInv();
requires call Yield_GarbageCollect_100(tid);
requires call Yield_CollectorPhase_100(tid, IDLE());
requires call Yield_SweepPtr_100(tid, memHi);
{
    var nextPhase: int;

    while (*)
    invariant {:yields} true;
    invariant call Yield_Iso();
    invariant call Yield_MsWellFormed(tid, 0);
    invariant call Yield_RootScanBarrierInv();
    invariant call Yield_GarbageCollect_100(tid);
    invariant call Yield_CollectorPhase_100(tid, IDLE());
    invariant call Yield_SweepPtr_100(tid, memHi);
    {
        call nextPhase := HandshakeCollector(tid); // IDLE --> MARK
        par YieldWaitForMutators(tid, collectorPhase, false, 0) |
            Yield_Iso() |
            Yield_MsWellFormed(tid, 0) |
            Yield_RootScanBarrierInv() |
            Yield_GarbageCollect_100(tid) |
            Yield_CollectorPhase_100(tid, collectorPhase) |
            Yield_SweepPtr_100(tid, sweepPtr);
        call WaitForMutators(tid, nextPhase);
        call MarkOuterLoop(tid);
        call nextPhase := HandshakeCollector(tid); // MARK --> SWEEP
        par YieldWaitForMutators(tid, collectorPhase, false, 0) |
            Yield_Iso() |
            Yield_MsWellFormed(tid, 0) |
            Yield_RootScanBarrierInv() |
            Yield_GarbageCollect_100(tid) |
            Yield_CollectorPhase_100(tid, collectorPhase) |
            Yield_SweepPtr_100(tid, sweepPtr);
        call WaitForMutators(tid, nextPhase);
        call Sweep(tid);
        call nextPhase := HandshakeCollector(tid); // SWEEP --> IDLE
    }
}

yield procedure {:layer 100}
MarkOuterLoop({:linear "tid"} tid:Tid)
preserves call Yield_Iso();
requires call YieldMarkBegin(tid, old(Color));
ensures call YieldMarkEnd(tid);
preserves call Yield_MsWellFormed(tid, 0);
preserves call Yield_CollectorPhase_98(tid, old(collectorPhase));
preserves call Yield_RootScanBarrierInv();
{
    var canStop: bool;

    call ResetSweepPtr(tid);
    while (true)
    invariant {:yields} true;
    invariant call YieldMark(tid, old(Color));
    invariant call Yield_MsWellFormed(tid, 0);
    invariant call Yield_CollectorPhase_98(tid, old(collectorPhase));
    invariant call Yield_RootScanBarrierInv();
    {
        call canStop := CanMarkStop(tid);
        if (canStop)
        {
            return;
        }
        call MarkInnerLoop(tid);
    }
}

yield procedure {:layer 100}
MarkInnerLoop({:linear "tid"} tid:Tid)
preserves call Yield_Iso();
preserves call YieldMark(tid, old(Color));
preserves call Yield_MsWellFormed(tid, 0);
preserves call Yield_CollectorPhase_98(tid, old(collectorPhase));
preserves call Yield_RootScanBarrierInv();
{
    var nodeProcessed:int;
    var fldIter: int;
    var isEmpty: bool;
    var child: int;

    while (true)
    invariant {:yields} true;
    invariant call YieldMark(tid, old(Color));
    invariant call Yield_MsWellFormed(tid, 0);
    invariant call Yield_CollectorPhase_98(tid, old(collectorPhase));
    invariant call Yield_RootScanBarrierInv();
    {
        call isEmpty, nodeProcessed := SET_Peek(tid);
        if (isEmpty) {
            break;
        }
        fldIter := 0;
        while (fldIter < numFields)
        invariant {:yields} true;
        invariant call YieldMark(tid, old(Color));
        invariant call Yield_MsWellFormed(tid, nodeProcessed);
        invariant call Yield_CollectorPhase_98(tid, old(collectorPhase));
        invariant call Yield_RootScanBarrierInv();
        invariant call Yield_MarkInnerLoopFieldIter(tid, fldIter, nodeProcessed);
        {
            call child := ReadFieldCollector(tid, nodeProcessed, fldIter);
            if (memAddr(child))
            {
                call SET_InsertIntoSetIfWhite(tid, nodeProcessed, child);
            }
            fldIter := fldIter + 1;
        }
        call SET_RemoveFromSet(tid, nodeProcessed);
    }
}

yield procedure {:layer 100}
Sweep({:linear "tid"} tid:Tid)
requires {:layer 98,99,100} tid == GcTid;
preserves call Yield_Iso();
preserves call Yield_MsWellFormed(tid, 0);
preserves call Yield_RootScanBarrierInv();
requires call YieldSweepBegin(tid, false, old(Color));
ensures call YieldSweepEnd(tid);
{
    var localSweepPtr: int;
    var {:layer 100} snapColor: [int]int;

    localSweepPtr := memLo;
    call ClearToAbsWhite(tid);
    par YieldSweepBegin(tid, true, Color) | Yield_MsWellFormed(tid, 0) | Yield_RootScanBarrierInv() | Yield_Iso();

    call snapColor := GhostReadColor100();
    while (localSweepPtr < memHi)
    invariant {:yields} {:layer 96} true;
    invariant {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
    invariant {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
    invariant {:layer 100} SweepPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase);
    invariant {:layer 100} localSweepPtr == sweepPtr && memLo <= sweepPtr && sweepPtr <= memHi;
    invariant {:layer 100} (forall i: int :: rootAddr(i) && memAddr(root[i]) ==> Black(snapColor[root[i]]));
    invariant {:layer 100} SweepInvInit(root, rootAbs, mem, memAbs, snapColor, toAbs, allocSet);
    invariant {:layer 100} (forall i:int:: memAddr(i) ==> if sweepPtr <= i then Color[i] == snapColor[i] else if Black(snapColor[i]) then White(Color[i]) else Unalloc(Color[i]));
    {
        call SweepNext(tid);
        localSweepPtr := localSweepPtr + 1;
    }
}

//////////////////////////////////////////////////////////////////////////////
// Layer 99
//////////////////////////////////////////////////////////////////////////////

yield invariant {:layer 99} Yield_CollectorPhase_99({:linear "tid"} tid:Tid, tick_collectorPhase: int);
invariant tid == GcTid;
invariant tick_collectorPhase == collectorPhase;

yield invariant {:layer 99} Yield_SweepPtr_99({:linear "tid"} tid:Tid, tick_sweepPtr: int);
invariant tid == GcTid;
invariant tick_sweepPtr == sweepPtr;

yield invariant {:layer 99} Yield_RootScanBarrierInv();
invariant RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);

yield invariant {:layer 99} Yield_InitVars99({:linear "tid"} mutatorTids:[int]bool, tick_mutatorsInRootScanBarrier: [int]bool, tick_rootScanBarrier: int);
invariant (forall i:int :: mutatorId(i) ==> mutatorTids[i] && mutatorTids[-i]);
invariant mutatorsInRootScanBarrier == tick_mutatorsInRootScanBarrier;
invariant rootScanBarrier == tick_rootScanBarrier;

yield invariant {:layer 99} Yield_RootScanOn({:linear "tid"} tid: Tid, tick_rootScanOn: bool);
invariant tid == GcTid;
invariant rootScanOn == tick_rootScanOn;

yield invariant {:layer 99} Yield_RootScanBarrierEnter({:linear "tid"} tid: Tid);
invariant mutatorTidWhole(tid);
invariant !mutatorsInRootScanBarrier[tid->i];

yield invariant {:layer 99} Yield_RootScanBarrierWait({:linear "tid"} tid: Tid);
invariant mutatorTidLeft(tid);
invariant mutatorsInRootScanBarrier[tid->i];

yield procedure {:layer 99}
InitVars99({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool)
requires {:layer 98,99} gcAndMutatorTids(tid, mutatorTids);
ensures call Yield_InitVars98(tid, mutatorTids, 0);
requires call Yield_InitVars99(mutatorTids, old(mutatorsInRootScanBarrier), old(rootScanBarrier));
ensures call Yield_InitVars99(mutatorTids, old(mutatorsInRootScanBarrier), numMutators);
{
    call InitRootScanBarrier(tid, mutatorTids);
    call InitVars98(tid, mutatorTids);
}

yield procedure {:layer 99}
TestRootScanBarrier({:linear "tid"} tid:Tid)
requires {:layer 95,96} mutatorTidWhole(tid);
requires call Yield_RootScanBarrierEnter(tid);
requires call Yield_RootScanBarrierInv();
{
    var isRootScanOn: bool;
    var{:linear "tid"} tid_tmp: Tid;

    call isRootScanOn := PollMutatorReadBarrierOn(tid);
    par Yield_RootScanBarrierInv() | Yield_RootScanBarrierEnter(tid) | Yield_97() | Yield_98();
    if (isRootScanOn)
    {
        assert{:layer 99} mutatorsInRootScanBarrier == mutatorsInRootScanBarrier[tid->i := false];
        call tid_tmp := MutatorRootScanBarrierEnter(tid);
        par Yield_RootScanBarrierInv() | Yield_RootScanBarrierWait(tid_tmp) | Yield_97() | Yield_98();
        assert{:layer 99} mutatorsInRootScanBarrier == mutatorsInRootScanBarrier[tid_tmp->i := true];
        call tid_tmp := MutatorRootScanBarrierWait(tid_tmp);
        call TidOutput(tid_tmp, tid);
    }
}

>-< action {:layer 100} AtomicCanMarkStop({:linear "tid"} tid:Tid) returns (canStop: bool)
modifies Color;
{
    assert tid == GcTid;
    havoc Color;
    assume (forall u: int :: if memAddr(u) && White(old(Color)[u]) && (exists k: int :: rootAddr(k) && root[k] == u) then Color[u] == GRAY() else Color[u] == old(Color)[u]);
    canStop := (forall v: int :: memAddr(v) ==> !Gray(Color[v]));
}

yield procedure {:layer 99}
CanMarkStop({:linear "tid"} tid:Tid) returns (canStop: bool)
refines AtomicCanMarkStop;
requires {:layer 99} tid == GcTid;
preserves call Yield_MsWellFormed(tid, 0);
preserves call Yield_CollectorPhase_98(tid, old(collectorPhase));
preserves call Yield_RootScanBarrierInv();
{
    var i: int;
    var o: int;
    var {:layer 99} snapColor: [int]int;

    call CollectorRootScanBarrierStart(tid);

    par Yield_MsWellFormed(tid, 0) | Yield_CollectorPhase_98(tid, old(collectorPhase)) | Yield_RootScanBarrierInv() | Yield_RootScanOn(tid, true) | Yield_97();

    call snapColor := GhostReadColor99();
    call CollectorRootScanBarrierWait(tid);

    i := 0;
    while (i < numRoots)
    invariant {:yields} {:layer 98} true;
    invariant call Yield_MsWellFormed(tid, 0);
    invariant call Yield_CollectorPhase_98(tid, old(collectorPhase));
    invariant {:layer 99} Mutators == mutatorsInRootScanBarrier && rootScanOn;
    invariant {:layer 99} 0 <= i && i <= numRoots;
    invariant {:layer 99} Color == (lambda u: int :: if memAddr(u) && White(snapColor[u]) && (exists k: int :: 0 <= k && k < i && root[k] == u) then GRAY() else snapColor[u]);
    {
        call o := ReadRootInRootScanBarrier(tid, i);
        if (memAddr(o))
        {
            call InsertIntoSetIfWhiteInRootScanBarrier(tid, o);
        }
        i := i + 1;
    }
    call canStop := NoGrayInRootScanBarrier(tid);
    call CollectorRootScanBarrierEnd(tid);
}

>-< action {:layer 100} AtomicWriteFieldRaw({:linear "tid"} tid:Tid, x: idx, f: fld, y: idx)
modifies memAbs,  mem;
{
    assert mutatorTidWhole(tid) && rootAddr(x) && tidOwns(tid, x) && fieldAddr(f) && rootAddr(y) && tidOwns(tid, y) && memAddr(root[x]) && toAbs[root[x]] != nil && memAddrAbs(rootAbs[x]);
    memAbs[rootAbs[x]][f] := rootAbs[y];
    mem[root[x]][f] := root[y];
}

yield procedure {:layer 99} WriteFieldRaw({:linear "tid"} tid:Tid, x: idx, f: fld, y: idx)
refines AtomicWriteFieldRaw;
requires {:layer 98} mutatorTidWhole(tid);
{
    var valx: int;
    var valy: int;

    call valx := ReadRoot(tid, x);
    call valy := ReadRoot(tid, y);
    call WriteFieldGeneral(tid, valx, f, valy);
    call SetMemAbs1(x, f, y);
}

>-< action {:layer 100} AtomicReadFieldRaw({:linear "tid"} tid:Tid, x: idx, f: fld, y: idx)
modifies rootAbs, root;
{
    assert mutatorTidWhole(tid) && rootAddr(x) && tidOwns(tid, x) && fieldAddr(f) && rootAddr(y) && tidOwns(tid, y) && memAddr(root[x]) && toAbs[root[x]] != nil && memAddrAbs(rootAbs[x]);
    rootAbs[y] := memAbs[rootAbs[x]][f];
    root[y] := mem[root[x]][f];
}

yield procedure {:layer 99} ReadFieldRaw({:linear "tid"} tid:Tid, x: idx, f: fld, y: idx)
refines AtomicReadFieldRaw;
{
    var valx: int;
    var valy: int;

    call valx := ReadRoot(tid, x);
    call valy := ReadFieldGeneral(tid, valx, f);
    call WriteRoot(tid, y, valy);
    call SetRootAbs1(x, f, y);
}

>-< action {:layer 100} AtomicEqRaw({:linear "tid"} tid:Tid, x: idx, y:idx) returns (isEqual:bool)
{ assert mutatorTidWhole(tid) && rootAddr(x) && tidOwns(tid, x) && rootAddr(y) && tidOwns(tid, y); isEqual := root[x] == root[y]; }

yield procedure {:layer 99} EqRaw({:linear "tid"} tid:Tid, x: idx, y:idx) returns (isEqual:bool)
refines AtomicEqRaw;
{
    var vx:int;
    var vy:int;

    call vx := ReadRoot(tid, x);
    call vy := ReadRoot(tid, y);
    isEqual := vx == vy;
}

>-< action {:layer 100} AtomicAllocRaw({:linear "tid"} tid:Tid, y:idx) returns (ptr: int, absPtr: obj)
modifies allocSet, rootAbs, root, toAbs, memAbs, Color, mem;
{
    assert mutatorTidWhole(tid) && rootAddr(y) && tidOwns(tid, y);
    assert (forall x: int, f: fld :: memAddr(x) && Unalloc(Color[x]) ==> toAbs[x] == nil);
    assume(memAddr(ptr) && Unalloc(Color[ptr]));
    assume(memAddrAbs(absPtr) && !allocSet[absPtr] && absPtr != nil);
    allocSet[absPtr] := true;
    rootAbs[y] := absPtr;
    root[y] := ptr;
    toAbs[ptr] := absPtr;
    memAbs[absPtr] := (lambda z: int :: if (fieldAddr(z)) then absPtr else memAbs[absPtr][z]);
    Color[ptr] := if sweepPtr <= ptr then BLACK() else WHITE();
    mem[ptr] := (lambda z: int :: if (fieldAddr(z)) then ptr else mem[ptr][z]);
}

yield procedure {:layer 99} AllocRaw({:linear "tid"} tid:Tid, y:idx) returns (ptr: int, absPtr: obj)
refines AtomicAllocRaw;
{
    call absPtr := PrimitiveFindFreePtrAbs();
    call ptr := FindFreePtr(tid, absPtr);
    call WriteRoot(tid, y, ptr);
    call SetMemAbs2(absPtr);
    call SetRootAbs2(y, absPtr);
}

>-< action {:layer 100} AtomicWriteBarrier({:linear "tid"} tid:Tid, y:idx)
modifies Color;
{
    var val:int;
    assert mutatorTidWhole(tid) && rootAddr(y) && tidOwns(tid, y);
    val := root[y];
    if (MarkPhase(mutatorPhase[tid->i]) && memAddr(val) && White(Color[val])) {
        Color[val] := GRAY();
    }
}

yield procedure {:layer 99} WriteBarrier({:linear "tid"} tid:Tid, y:idx)
refines AtomicWriteBarrier;
requires {:layer 98} mutatorTidWhole(tid);
{
    var phase: int;
    var rootVal: int;

    call rootVal := ReadRoot(tid, y);
    if (memAddr(rootVal))
    {
        call phase := ReadMutatorPhase(tid);
      if (MarkPhase(phase))
        {
            call SET_InsertIntoSetIfWhiteByMutator(tid, rootVal);
        }
    }
}

//////////////////////////////////////////////////////////////////////////////
// Layer 98
//////////////////////////////////////////////////////////////////////////////

yield invariant {:layer 98} Yield_MsWellFormed({:linear "tid"} tid:Tid, nodePeeked: int);
invariant tid == GcTid;
invariant MsWellFormed(MarkStack, MarkStackPtr, Color, nodePeeked);

yield invariant {:layer 98} Yield_CollectorPhase_98({:linear "tid"} tid:Tid, tick_collectorPhase: int);
invariant tid == GcTid;
invariant tick_collectorPhase == collectorPhase;

yield invariant {:layer 98} Yield_SweepPtr_98({:linear "tid"} tid:Tid, tick_sweepPtr: int);
invariant tid == GcTid;
invariant tick_sweepPtr == sweepPtr;

yield invariant {:layer 98} Yield_MarkPhase({:linear "tid"} tid:Tid, ptr: int);
invariant mutatorTidWhole(tid);
invariant MarkPhase(mutatorPhase[tid->i]);

yield invariant {:layer 98} Yield_98();

yield invariant {:layer 98} Yield_InitVars98({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool, tick_MarkStackPtr: int);
invariant gcAndMutatorTids(tid, mutatorTids);
invariant MarkStackPtr == tick_MarkStackPtr;

yield procedure {:layer 98}
InitVars98({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool)
requires call Yield_InitVars98(tid, mutatorTids, old(MarkStackPtr));
ensures call Yield_InitVars98(tid, mutatorTids, 0);
{
    call InitMarkStackPtr(tid, mutatorTids);
}

>-< action {:layer 99} AtomicFindFreePtr({:linear "tid"} tid: Tid, absPtr: obj) returns (ptr: int)
modifies Color, toAbs, mem;
{
    assert mutatorTidWhole(tid);
    assert (forall x: int :: memAddr(x) && Unalloc(Color[x]) ==> toAbs[x] == nil);
    assume (memAddr(ptr) && Unalloc(Color[ptr]));
    Color[ptr] := if sweepPtr <= ptr then BLACK() else WHITE();
    toAbs[ptr] := absPtr;
    mem[ptr] := (lambda z: int :: if (fieldAddr(z)) then ptr else mem[ptr][z]);
}

yield procedure {:layer 98} FindFreePtr({:linear "tid"} tid: Tid, absPtr: obj) returns (ptr: int)
refines AtomicFindFreePtr;
{
    var iter: int;
    var spaceFound: bool;

    spaceFound := false;
    while (true)
    invariant {:yields} true;
    invariant {:layer 98} !spaceFound;
    {
        iter := memLo;
        while (iter < memHi)
        invariant {:yields} true;
        invariant {:layer 98} !spaceFound;
        invariant {:layer 98} memLo <= iter && iter <= memHi;
        {
            call spaceFound := AllocIfPtrFree(tid, iter, absPtr);
            if (spaceFound)
            {
                ptr := iter;
                return;
            }
            else
            {
                iter := iter + 1;
            }
        }
    }
}

>-< action {:layer 99} AtomicSET_InsertIntoSetIfWhiteByMutator({:linear "tid"} tid:Tid, memLocal:int)
modifies Color;
{
    assert mutatorTidWhole(tid) && memAddr(memLocal) && MarkPhase(mutatorPhase[tid->i]);
    if (White(Color[memLocal])) {
        Color[memLocal] := GRAY();
    }
}

yield procedure {:layer 98}
SET_InsertIntoSetIfWhiteByMutator({:linear "tid"} tid:Tid, memLocal:int)
refines AtomicSET_InsertIntoSetIfWhiteByMutator;
preserves call Yield_MarkPhase(tid, memLocal);
{
    var color:int;

    call color := ReadColorByMutator3(tid, memLocal);
    if (!White(color))
    {
        return;
    }

    par Yield_97() | Yield_MarkPhase(tid, memLocal);

    call MsPushByMutator(tid, memLocal);
    assert {:layer 98} MST(MarkStackPtr-1);
}

<- action {:layer 99} AtomicNoGrayInRootScanBarrier({:linear "tid"} tid:Tid) returns (noGray: bool)
{
    assert tid == GcTid && rootScanOn && mutatorsInRootScanBarrier == Mutators;
    noGray := (forall i: int :: memAddr(i) ==> !Gray(Color[i]));
}

yield procedure {:layer 98}
NoGrayInRootScanBarrier({:linear "tid"} tid:Tid) returns (noGray: bool)
refines AtomicNoGrayInRootScanBarrier;
preserves call Yield_MsWellFormed(tid, 0);
preserves call Yield_CollectorPhase_98(tid, old(collectorPhase));
{
    call noGray := MsIsEmpty(tid);
    assert {:layer 98} noGray || MST(0);
}

<- action {:layer 99} AtomicInsertIntoSetIfWhiteInRootScanBarrier({:linear "tid"} tid:Tid, memLocal:int)
modifies Color;
{
    assert tid == GcTid && rootScanOn && mutatorsInRootScanBarrier == Mutators && memAddr(memLocal);
    if (White(Color[memLocal])) {
        Color[memLocal] := GRAY();
    }
}

yield procedure {:layer 98}
InsertIntoSetIfWhiteInRootScanBarrier({:linear "tid"} tid:Tid, memLocal:int)
refines AtomicInsertIntoSetIfWhiteInRootScanBarrier;
preserves call Yield_MsWellFormed(tid, 0);
preserves call Yield_CollectorPhase_98(tid, old(collectorPhase));
{
    call MsPushByCollector(tid, memLocal);
    assert {:layer 98} MST(MarkStackPtr-1);
}

<- action {:layer 99,100} AtomicSET_InsertIntoSetIfWhite({:linear "tid"} tid:Tid, parent: int, child:int)
modifies Color;
{
    assert tid == GcTid;
    assert MarkPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase) && sweepPtr == memLo && memAddr(child);
    if (White(Color[child])) {
        Color[child] := GRAY();
    }
}

yield procedure {:layer 98}
SET_InsertIntoSetIfWhite({:linear "tid"} tid:Tid, parent: int, child:int)
refines AtomicSET_InsertIntoSetIfWhite;
requires {:layer 98} memAddr(parent) && memAddr(child);
preserves call Yield_MsWellFormed(tid, parent);
preserves call Yield_CollectorPhase_98(tid, old(collectorPhase));
{
    call MsPushByCollector(tid, child);
    assert {:layer 98} MST(MarkStackPtr-1);
}

-> action {:layer 99,100} AtomicSET_Peek({:linear "tid"} tid:Tid) returns (isEmpty: bool, val:int)
{
    assert tid == GcTid;
    assert MarkPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase);
    if (*) {
        assume (memAddr(val) && !Unalloc(Color[val]));
        isEmpty := false;
    } else {
        isEmpty := true;
    }
}

yield procedure {:layer 98}
SET_Peek({:linear "tid"} tid:Tid) returns (isEmpty: bool, val:int)
refines AtomicSET_Peek;
requires call Yield_MsWellFormed(tid, 0);
ensures call Yield_MsWellFormed(tid, if isEmpty then 0 else val);
preserves call Yield_CollectorPhase_98(tid, old(collectorPhase));
{
    assert {:layer 98} MST(MarkStackPtr - 1);
    call isEmpty, val := MsPop(tid);
}

//////////////////////////////////////////////////////////////////////////////
// Layer 97
//////////////////////////////////////////////////////////////////////////////

yield invariant {:layer 97} Yield_97();

yield invariant {:layer 97} YieldWaitForMutators({:linear "tid"} tid:Tid, nextPhase: int, done: bool, i: int);
invariant tid == GcTid;
invariant nextPhase == collectorPhase;
invariant done ==> (forall j:int:: 1 <= j && j < i ==> nextPhase == mutatorPhase[j]);

>-< action {:layer 98,100} AtomicWaitForMutators({:linear "tid"} tid:Tid, nextPhase: int)
{
    assert tid == GcTid;
    assume (forall j:int:: mutatorId(j) ==> nextPhase == mutatorPhase[j]);
}

yield procedure {:layer 97}
WaitForMutators({:linear "tid"} tid:Tid, nextPhase: int)
refines AtomicWaitForMutators;
requires call YieldWaitForMutators(tid, nextPhase, false, 0);
{
    var done: bool;
    var i: int;
    var mutatorPhaseLocal: int;

    done := false;
    call YieldWaitForMutators(tid, nextPhase, done, 1);
    while (!done)
    invariant {:yields} true;
    invariant call YieldWaitForMutators(tid, nextPhase, done, numMutators+1);
    {
        done := true;
        i := 1;
        call YieldWaitForMutators(tid, nextPhase, done, i);
        while (i <= numMutators)
          invariant {:yields} true;
          invariant call YieldWaitForMutators(tid, nextPhase, done, i);
        {
            call mutatorPhaseLocal := ReadMutatorPhaseByCollector(tid, i);
            if (nextPhase != mutatorPhaseLocal)
            {
                done := false;
            }
            i := i + 1;
        }
    }
}

//////////////////////////////////////////////////////////////////////////////
// Layer 96
//////////////////////////////////////////////////////////////////////////////

>-< action {:layer 97,100} AtomicInitVars100({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool)
modifies mutatorPhase, root, toAbs, Color, mem, collectorPhase, sweepPtr;
{
    assert tid == GcTid;
    assert (forall i:int :: mutatorId(i) ==> mutatorTids[i] && mutatorTids[-i]);
    havoc mem, root, Color, mutatorPhase;
    assume (forall x: int, f: fld :: memAddr(x) && fieldAddr(f) ==> mem[x][f] == x);
    assume (forall x: idx :: rootAddr(x) ==> root[x] == 0);
    assume (forall i:int :: memAddr(i) ==> Color[i] == UNALLOC());
    assume (forall i:int :: mutatorId(i) ==> mutatorPhase[i] == IDLE());
    toAbs := (lambda i:int :: if memAddr(i) then nil else Int(i));
    collectorPhase := IDLE();
    sweepPtr := memHi;
}

yield procedure {:layer 96} InitVars100({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool)
refines AtomicInitVars100;
{
    var n:int;
    var m:int;

    n := memLo;
    while (n < memHi)
        invariant{:yields} {:layer 95} true;
        invariant{:layer 96} memLo <= n && n <= memHi;
        invariant{:layer 96} (forall i:int, f: fld :: memLo <= i && i < n && fieldAddr(f) ==> mem[i][f] == i);
    {
        m := 0;
        while (m < numFields)
            invariant{:yields} {:layer 95} true;
            invariant{:layer 96} 0 <= m && m <= numFields;
            invariant{:layer 96} (forall i:int, f: fld :: memLo <= i && i < n && fieldAddr(f) ==> mem[i][f] == i);
            invariant{:layer 96} (forall f: fld :: 0 <= f && f < m ==> mem[n][f] == n);
        {
            call InitField(tid, mutatorTids, n, m);
            m := m + 1;
        }

        call InitColor(tid, mutatorTids, n);
        n := n + 1;
    }

    n := 0;
    while (n < numRoots)
        invariant{:yields} {:layer 95} true;
        invariant{:layer 96} 0 <= n && n <= numRoots;
        invariant{:layer 96} (forall i:int :: 0 <= i && i < n ==> root[i] == 0);
    {
        call InitRoot(tid, mutatorTids, n);
        n := n + 1;
    }

    n := memLo;
    while (n < memHi)
        invariant{:yields} {:layer 95} true;
        invariant{:layer 96} memLo <= n && n <= memHi;
        invariant{:layer 96} (forall i:int :: memLo <= i && i < n ==> Color[i] == UNALLOC());
    {
        call InitColor(tid, mutatorTids, n);
        n := n + 1;
    }

    n := 1;
    while (n <= numMutators)
        invariant{:yields} {:layer 95} true;
        invariant{:layer 96} 1 <= n && n <= numMutators + 1;
        invariant{:layer 96} (forall i:int :: mutatorId(i) && i < n ==> mutatorPhase[i] == IDLE());
    {
        call InitMutatorPhase(tid, mutatorTids, n);
        n := n + 1;
    }

    call InitToAbs(tid, mutatorTids);
    call InitCollectorPhase(tid, mutatorTids);
    call InitSweepPtr(tid, mutatorTids);
}

>-< action {:layer 97,100} AtomicSET_RemoveFromSet({:linear "tid"} tid:Tid, scannedLocal:int)
modifies Color;
{
    assert MarkPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase);
    assert tid == GcTid;
    assert memAddr(scannedLocal);
    Color[scannedLocal] := BLACK();
}

yield procedure {:layer 96} SET_RemoveFromSet({:linear "tid"} tid:Tid, scannedLocal:int)
refines AtomicSET_RemoveFromSet;
{
    call LockAcquire(tid);
    call SetColor2(tid, scannedLocal, BLACK());
    call LockRelease(tid);
}

>-< action {:layer 97,98} AtomicMsPushByCollector({:linear "tid"} tid: Tid, val: int)
modifies Color, MarkStack, MarkStackPtr;
{
    assert memAddr(val) && tid == GcTid;
    if (White(Color[val])) {
        Color[val] := GRAY();
        MarkStack[MarkStackPtr] := val;
        MarkStackPtr := MarkStackPtr + 1;
    }
}

yield procedure {:layer 96} MsPushByCollector({:linear "tid"} tid: Tid, val: int)
refines AtomicMsPushByCollector;
{
    var color:int;
    var stack:int;

    call LockAcquire(tid);
    call color := ReadColorByCollector(tid, val);
    if (White(color))
    {
        call SetColor2(tid, val, GRAY());
        call stack := ReadMarkStackPtr(tid);
        call WriteMarkStack(tid, stack, val);
        stack := stack + 1;
        call SetMarkStackPtr(tid, stack);
    }
    call LockRelease(tid);
}

>-< action {:layer 97,98} AtomicMsPushByMutator({:linear "tid"} tid: Tid, val: int)
modifies Color, MarkStack, MarkStackPtr;
{
    assert memAddr(val) && mutatorTidWhole(tid) && MarkPhase(mutatorPhase[tid->i]);
    if (White(Color[val])) {
        Color[val] := GRAY();
        MarkStack[MarkStackPtr] := val;
        MarkStackPtr := MarkStackPtr + 1;
    }
}

yield procedure {:layer 96} MsPushByMutator({:linear "tid"} tid: Tid, val: int)
refines AtomicMsPushByMutator;
{
    var color:int;
    var stack:int;

    call LockAcquire(tid);
    call color := ReadColorByMutator2(tid, val);
    if (White(color))
    {
        call SetColor2(tid, val, GRAY());
        call stack := ReadMarkStackPtr(tid);
        call WriteMarkStack(tid, stack, val);
        stack := stack + 1;
        call SetMarkStackPtr(tid, stack);
    }
    call LockRelease(tid);
}

>-< action {:layer 97,98} AtomicMsPop({:linear "tid"} tid:Tid) returns (isEmpty: bool, val:int)
modifies MarkStackPtr;
{
    assert tid == GcTid;
    if (MarkStackPtr > 0) {
        MarkStackPtr := MarkStackPtr - 1;
        val := MarkStack[MarkStackPtr];
        isEmpty := false;
    } else {
        val := 0;
        isEmpty := true;
    }
}

yield procedure {:layer 96} MsPop({:linear "tid"} tid:Tid) returns (isEmpty: bool, val:int)
refines AtomicMsPop;
{
    var stack:int;

    call LockAcquire(tid);
    call stack := ReadMarkStackPtr(tid);
    if (stack > 0)
    {
        stack := stack - 1;
        call SetMarkStackPtr(tid, stack);
        call val := ReadMarkStack(tid, stack);
        isEmpty := false;
    }
    else
    {
        val := 0;
        isEmpty := true;
    }
    call LockRelease(tid);
}

>-< action {:layer 97,98} AtomicMsIsEmpty({:linear "tid"} tid: Tid) returns (isEmpty: bool)
{ assert tid == GcTid; isEmpty := MarkStackPtr == 0; }

yield procedure {:layer 96} MsIsEmpty({:linear "tid"} tid: Tid) returns (isEmpty: bool)
refines AtomicMsIsEmpty;
{
    var v:int;

    call LockAcquire(tid);
    call v := ReadMarkStackPtr(tid);
    isEmpty := v == 0;
    call LockRelease(tid);
}

>-< action {:layer 97,100} AtomicResetSweepPtr({:linear "tid"} tid:Tid)
modifies sweepPtr;
{ assert tid == GcTid; sweepPtr := memLo; }

yield procedure {:layer 96} ResetSweepPtr({:linear "tid"} tid:Tid)
refines AtomicResetSweepPtr;
{
    call LockAcquire(tid);
    call SetSweepPtrLocked(tid, memLo);
    call LockRelease(tid);
}

<- action {:layer 97,100} AtomicSweepNext({:linear "tid"} tid:Tid)
modifies Color, sweepPtr;
{
    assert SweepPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase);
    assert !Gray(Color[sweepPtr]);
    assert tid == GcTid;
    assert memAddr(sweepPtr);
    Color[sweepPtr] := if White(Color[sweepPtr]) then UNALLOC() else if Black(Color[sweepPtr]) then WHITE() else Color[sweepPtr];
    sweepPtr := sweepPtr + 1;
}

yield procedure {:layer 96} SweepNext({:linear "tid"} tid:Tid)
refines AtomicSweepNext;
{
    var color:int;
    var sweep:int;

    call LockAcquire(tid);
    call sweep := ReadSweepPtr(tid);
    call color := ReadColorByCollector(tid, sweep);
    color := if White(color) then UNALLOC() else if Black(color) then WHITE() else color;
    call SetColor(tid, sweep, color);
    sweep := sweep + 1;
    call SetSweepPtrLocked(tid, sweep);
    call LockRelease(tid);
}

>-< action {:layer 97,100} AtomicHandshakeCollector({:linear "tid"} tid:Tid) returns (nextPhase: int)
modifies collectorPhase;
{
    assert tid == GcTid;
    if (IdlePhase(collectorPhase)) {
        collectorPhase := MARK();
        nextPhase := MARK();
    } else if (MarkPhase(collectorPhase)) {
        collectorPhase := SWEEP();
        nextPhase := SWEEP();
    } else {
        //assume (SweepPhase(collectorPhase));
        collectorPhase := IDLE();
        nextPhase := IDLE();
    }
}

yield procedure {:layer 96} HandshakeCollector({:linear "tid"} tid:Tid) returns (nextPhase: int)
refines AtomicHandshakeCollector;
{
    var phase:int;

    call LockAcquire(tid);
    call phase := ReadCollectorPhase(tid);
    nextPhase := if IdlePhase(phase) then MARK() else if MarkPhase(phase) then SWEEP() else IDLE();
    call SetCollectorPhase(tid, nextPhase);
    call LockRelease(tid);
}

>-< action {:layer 97,100} AtomicUpdateMutatorPhase({:linear "tid"} tid: Tid)
modifies mutatorPhase;
{ assert mutatorTidWhole(tid); mutatorPhase[tid->i] := collectorPhase; }

yield procedure {:layer 96} UpdateMutatorPhase({:linear "tid"} tid: Tid)
refines AtomicUpdateMutatorPhase;
{
    var p:int;

    call LockAcquire(tid);
    call p := ReadCollectorPhaseLocked(tid);
    call SetMutatorPhaseLocked(tid, p);
    call LockRelease(tid);
}

>-< action {:layer 97,99} AtomicCollectorRootScanBarrierStart({:linear "tid"} tid: Tid)
modifies rootScanOn;
{ assert tid == GcTid; rootScanOn := true; }

yield procedure {:layer 96} CollectorRootScanBarrierStart({:linear "tid"} tid: Tid)
refines AtomicCollectorRootScanBarrierStart;
{
    call LockAcquire(tid);
    call CollectorRootScanBarrierStartLocked(tid);
    call LockRelease(tid);
}

<- action {:layer 97,99} AtomicCollectorRootScanBarrierEnd({:linear "tid"} tid: Tid)
modifies rootScanOn;
{ assert tid == GcTid; rootScanOn := false; }

yield procedure {:layer 96} CollectorRootScanBarrierEnd({:linear "tid"} tid: Tid)
refines AtomicCollectorRootScanBarrierEnd;
{
    call LockAcquire(tid);
    call CollectorRootScanBarrierEndLocked(tid);
    call LockRelease(tid);
}

>-< action {:layer 97,99} AtomicCollectorRootScanBarrierWait({:linear "tid"} tid: Tid)
{ assert tid == GcTid; assume rootScanBarrier == 0; }

yield procedure {:layer 96} CollectorRootScanBarrierWait({:linear "tid"} tid: Tid)
refines AtomicCollectorRootScanBarrierWait;
{
    var v:int;

    while (true)
    invariant {:yields} true;
    {
        call v := CollectorRootScanBarrierRead(tid);
        if (v == 0)
        {
            return;
        }
    }
}

>-< action {:layer 97,99} AtomicMutatorRootScanBarrierEnter({:linear_in "tid"} tid: Tid) returns({:linear "tid"} tid_left: Tid)
modifies rootScanBarrier, mutatorsInRootScanBarrier;
{
    assert mutatorTidWhole(tid);
    rootScanBarrier := rootScanBarrier - 1;
    mutatorsInRootScanBarrier[tid->i] := true;
    tid_left := Tid(tid->i, true, false);
}

yield procedure {:layer 96} MutatorRootScanBarrierEnter({:linear_in "tid"} tid: Tid) returns({:linear "tid"} tid_left: Tid)
refines AtomicMutatorRootScanBarrierEnter;
requires {:layer 95} mutatorTidWhole(tid);
ensures {:layer 95,96} tid_left->i == tid->i && tid_left->left;
{
    var{:linear "tid"} tid_right: Tid;

    call tid_left, tid_right := TidSplit(tid);
    call LockAcquire(tid_left);
    call MutatorsInRootScanBarrierAdd(tid_left, tid_right);
    call AddRootScanBarrier(tid_left, -1);
    call LockRelease(tid_left);
}

>-< action {:layer 97,99} AtomicMutatorRootScanBarrierWait({:linear_in "tid"} tid_left: Tid) returns({:linear "tid"} tid: Tid)
modifies rootScanBarrier, mutatorsInRootScanBarrier;
{
    assert mutatorTidLeft(tid_left) && mutatorsInRootScanBarrier[tid_left->i];
    assume !rootScanOn;
    rootScanBarrier := rootScanBarrier + 1;
    mutatorsInRootScanBarrier[tid_left->i] := false;
    tid := Tid(tid_left->i, true, true);
}

yield procedure {:layer 96} MutatorRootScanBarrierWait({:linear_in "tid"} tid_left: Tid) returns({:linear "tid"} tid: Tid)
refines AtomicMutatorRootScanBarrierWait;
ensures {:layer 95,96} tid->i == tid_left->i && tid->left && tid->right;
{
    var{:linear "tid"} tid_right: Tid;
    var b:bool;

    loop:
        assert {:yields} {:layer 96} true;
        call LockAcquire(tid_left);
        call b := MutatorReadBarrierOn(tid_left);
        if (!b)
        {
            call AddRootScanBarrier(tid_left, 1);
            call tid_right := MutatorsInRootScanBarrierRemove(tid_left);
            call LockRelease(tid_left);
            call tid := TidCombine(tid_left, tid_right);
            return;
        }
        call LockRelease(tid_left);
        goto loop;
}

>-< action {:layer 97,98} AtomicAllocIfPtrFree({:linear "tid"} tid:Tid, ptr:int, absPtr:obj) returns (spaceFound:bool)
modifies Color, toAbs, mem;
{
    assert mutatorTidWhole(tid) && memAddr(ptr) && (Unalloc(Color[ptr]) ==> toAbs[ptr] == nil);
    if (*) {
        assume Unalloc(Color[ptr]);
        Color[ptr] := if sweepPtr <= ptr then BLACK() else WHITE();
        toAbs[ptr] := absPtr;
        mem[ptr] := (lambda z: int :: if (fieldAddr(z)) then ptr else mem[ptr][z]);
        spaceFound := true;
    } else {
        spaceFound := false;
    }
}

yield procedure {:layer 96} AllocIfPtrFree({:linear "tid"} tid:Tid, ptr:int, absPtr:obj) returns (spaceFound:bool)
refines AtomicAllocIfPtrFree;
{
    var color:int;
    var sweep:int;
    var t:[int]obj;
    var fldIter:fld;
    var {:layer 96} snapMem: [int][fld]int;

    call color := ReadColorByMutator1(tid, ptr);
    if (Unalloc(color))
    {
        call Yield();
        call LockAcquire(tid);
        call color := ReadColorByMutator2(tid, ptr);
        if (Unalloc(color))
        {
            spaceFound := true;
            call sweep := ReadSweepPtr(tid);
            if (sweep <= ptr)
            {
                color := BLACK();
            }
            else
            {
                color := WHITE();
            }

            call snapMem := GhostReadMem();
            fldIter := 0;
            while (fldIter < numFields)
            invariant {:yields} {:layer 95} true;
            invariant {:layer 96} 0 <= fldIter && fldIter <= numFields;
            invariant {:layer 96} mem == snapMem[ptr := (lambda z: int :: if (0 <= z && z < fldIter) then ptr else snapMem[ptr][z])];
            {
                call InitializeFieldInAlloc(tid, ptr, fldIter);
                fldIter := fldIter + 1;
            }

            call SetColor3(tid, ptr, color, absPtr);
            call LockRelease(tid);
            return;
        }
        call LockRelease(tid);
    }
    spaceFound := false;
}

>-< action {:layer 97,100} AtomicIsWhiteByCollector({:linear "tid"} tid:Tid, i: int) returns (isWhite: bool)
{ assert tid == GcTid && memAddr(i); isWhite := White(Color[i]); }

yield procedure {:layer 96} IsWhiteByCollector({:linear "tid"} tid:Tid, i: int) returns (isWhite: bool)
refines AtomicIsWhiteByCollector;
{
    var v:int;

    call LockAcquire(tid);
    call v := ReadColorByCollector(tid, i);
    isWhite := White(v);
    call LockRelease(tid);
}

>-< action {:layer 97,100} AtomicClearToAbsWhite({:linear "tid"} tid:Tid)
modifies toAbs;
{ assert tid == GcTid; toAbs := (lambda x: int :: if memAddr(x) && White(Color[x]) then nil else toAbs[x]); }

yield procedure {:layer 96} ClearToAbsWhite({:linear "tid"} tid:Tid)
refines AtomicClearToAbsWhite;
{
    call LockAcquire(tid);
    call LockedClearToAbsWhite(tid);
    call LockRelease(tid);
}

yield invariant {:layer 96} Yield();

//////////////////////////////////////////////////////////////////////////////
// Layer 95
//////////////////////////////////////////////////////////////////////////////

>-< action {:layer 96} AtomicLockedClearToAbsWhite({:linear "tid"} tid:Tid)
modifies toAbs;
{ assert tid == GcTid && tidHasLock(tid, lock); toAbs := (lambda x: int :: if memAddr(x) && White(Color[x]) then nil else toAbs[x]); }

yield procedure {:layer 95} LockedClearToAbsWhite({:linear "tid"} tid:Tid)
refines AtomicLockedClearToAbsWhite;
{
    call SetToAbs1();
}

<-> action {:layer 96,99} AtomicInitField({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool, x: int, f: int)
modifies mem;
{ assert gcAndMutatorTids(tid, mutatorTids) && memAddr(x) && fieldAddr(f); mem[x][f] := x; }

yield procedure {:layer 95} InitField({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool, x: int, f: int)
refines AtomicInitField;
{
    call PrimitiveWriteField(x, f, x);
}

>-< action {:layer 96,100} AtomicReadFieldCollector({:linear "tid"} tid:Tid, x:int, f: fld) returns (y: int)
{ assert tid == GcTid && memAddr(x) && fieldAddr(f) && toAbs[x] != nil; y := mem[x][f]; }

yield procedure {:layer 95} ReadFieldCollector({:linear "tid"} tid:Tid, x:int, f: fld) returns (y: int)
refines AtomicReadFieldCollector;
{
    call y := PrimitiveReadField(x, f);
}

>-< action {:layer 96,99} AtomicReadFieldGeneral({:linear "tid"} tid:Tid, x: int, f: fld) returns (y: int)
{ assert mutatorTidWhole(tid) && memAddr(x) && fieldAddr(f) && toAbs[x] != nil; y := mem[x][f]; }

yield procedure {:layer 95} ReadFieldGeneral({:linear "tid"} tid:Tid, x: int, f: fld) returns (y: int)
refines AtomicReadFieldGeneral;
{
    call y := PrimitiveReadField(x, f);
}

>-< action {:layer 96,99} AtomicWriteFieldGeneral({:linear "tid"} tid:Tid, x: int, f: fld, y: int)
modifies mem;
{ assert mutatorTidWhole(tid) && memAddr(x) && fieldAddr(f) && toAbs[x] != nil; mem[x][f] := y; }

yield procedure {:layer 95} WriteFieldGeneral({:linear "tid"} tid:Tid, x: int, f: fld, y: int)
refines AtomicWriteFieldGeneral;
{
    call PrimitiveWriteField(x, f, y);
}

-> action {:layer 96} AtomicInitializeFieldInAlloc({:linear "tid"} tid: Tid, ptr: int, fld: int)
modifies mem;
{ assert mutatorTidWhole(tid) && tidHasLock(tid, lock) && memAddr(ptr) && fieldAddr(fld) && toAbs[ptr] == nil; mem[ptr][fld] := ptr; }

yield procedure {:layer 95} InitializeFieldInAlloc({:linear "tid"} tid: Tid, ptr: int, fld: int)
refines AtomicInitializeFieldInAlloc;
{
    call PrimitiveWriteField(ptr, fld, ptr);
}

<-> action {:layer 96} AtomicReadMarkStackPtr({:linear "tid"} tid:Tid) returns (val: int)
{ assert tidHasLock(tid, lock); val := MarkStackPtr; }

yield procedure {:layer 95} ReadMarkStackPtr({:linear "tid"} tid:Tid) returns (val: int)
refines AtomicReadMarkStackPtr;
{
    call val := PrimitiveReadMarkStackPtr();
}

>-< action {:layer 96,98} AtomicInitMarkStackPtr({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool)
modifies MarkStackPtr;
{ assert gcAndMutatorTids(tid, mutatorTids); MarkStackPtr := 0; }

yield procedure {:layer 95} InitMarkStackPtr({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool)
refines AtomicInitMarkStackPtr;
{
    call PrimitiveSetMarkStackPtr(0);
}

<-> action {:layer 96} AtomicSetMarkStackPtr({:linear "tid"} tid:Tid, val: int)
modifies MarkStackPtr;
{ assert tidHasLock(tid, lock); MarkStackPtr := val; }

yield procedure {:layer 95} SetMarkStackPtr({:linear "tid"} tid:Tid, val: int)
refines AtomicSetMarkStackPtr;
{
    call PrimitiveSetMarkStackPtr(val);
}

<-> action {:layer 96} AtomicReadMarkStack({:linear "tid"} tid:Tid, ptr: int) returns(val: int)
{ assert tidHasLock(tid, lock); val := MarkStack[ptr]; }

yield procedure {:layer 95} ReadMarkStack({:linear "tid"} tid:Tid, ptr: int) returns(val: int)
refines AtomicReadMarkStack;
{
    call val := PrimitiveReadMarkStack(ptr);
}

<-> action {:layer 96} AtomicWriteMarkStack({:linear "tid"} tid:Tid, ptr: int, val: int)
modifies MarkStack;
{ assert tidHasLock(tid, lock); MarkStack[ptr] := val; }

yield procedure {:layer 95} WriteMarkStack({:linear "tid"} tid:Tid, ptr: int, val: int)
refines AtomicWriteMarkStack;
{
    call PrimitiveWriteMarkStack(ptr, val);
}

<-> action {:layer 96,99} AtomicInitCollectorPhase({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool)
modifies collectorPhase;
{ assert gcAndMutatorTids(tid, mutatorTids); collectorPhase := IDLE(); }

yield procedure {:layer 95} InitCollectorPhase({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool)
refines AtomicInitCollectorPhase;
{
    call PrimitiveSetCollectorPhase(IDLE());
}

>-< action {:layer 96} AtomicReadCollectorPhase({:linear "tid"} tid: Tid) returns (phase:int)
{ assert tid == GcTid; phase := collectorPhase; }

yield procedure {:layer 95} ReadCollectorPhase({:linear "tid"} tid: Tid) returns (phase:int)
refines AtomicReadCollectorPhase;
{
    call phase := PrimitiveReadCollectorPhase();
}

-> action {:layer 96} AtomicReadCollectorPhaseLocked({:linear "tid"} tid: Tid) returns (phase:int)
{ assert mutatorTidWhole(tid) && tidHasLock(tid, lock); phase := collectorPhase; }

yield procedure {:layer 95} ReadCollectorPhaseLocked({:linear "tid"} tid: Tid) returns (phase:int)
refines AtomicReadCollectorPhaseLocked;
{
    call phase := PrimitiveReadCollectorPhase();
}

<-> action {:layer 96} AtomicSetCollectorPhase({:linear "tid"} tid: Tid, phase:int)
modifies collectorPhase;
{ assert tid == GcTid && tidHasLock(tid, lock); collectorPhase := phase; }

yield procedure {:layer 95} SetCollectorPhase({:linear "tid"} tid: Tid, phase:int)
refines AtomicSetCollectorPhase;
{
    call PrimitiveSetCollectorPhase(phase);
}

<-> action {:layer 96,99} AtomicInitMutatorPhase({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool, id: int)
modifies mutatorPhase;
{ assert gcAndMutatorTids(tid, mutatorTids); mutatorPhase[id] := IDLE(); }

yield procedure {:layer 95} InitMutatorPhase({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool, id: int)
refines AtomicInitMutatorPhase;
{
    call PrimitiveSetMutatorPhase(id, IDLE());
}

>-< action {:layer 96,100} AtomicReadMutatorPhaseByCollector({:linear "tid"} tid: Tid, i: int) returns (phase:int)
{ assert tid == GcTid; phase := mutatorPhase[i]; }

yield procedure {:layer 95} ReadMutatorPhaseByCollector({:linear "tid"} tid: Tid, i: int) returns (phase:int)
refines AtomicReadMutatorPhaseByCollector;
{
    call phase := PrimitiveReadMutatorPhase(i);
}

<-> action {:layer 96,99} AtomicReadMutatorPhase({:linear "tid"} tid: Tid) returns (phase:int)
{ assert mutatorTidWhole(tid); phase := mutatorPhase[tid->i]; }

yield procedure {:layer 95} ReadMutatorPhase({:linear "tid"} tid: Tid) returns (phase:int)
refines AtomicReadMutatorPhase;
{
    call phase := PrimitiveReadMutatorPhase(tid->i);
}

>-< action {:layer 96} AtomicSetMutatorPhaseLocked({:linear "tid"} tid: Tid, phase: int)
modifies mutatorPhase;
{ assert mutatorTidWhole(tid) && tidHasLock(tid, lock) && phase == collectorPhase; mutatorPhase[tid->i] := phase; }

yield procedure {:layer 95} SetMutatorPhaseLocked({:linear "tid"} tid: Tid, phase: int)
refines AtomicSetMutatorPhaseLocked;
{
    call PrimitiveSetMutatorPhase(tid->i, phase);
}

<-> action {:layer 96,99} AtomicInitSweepPtr({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool)
modifies sweepPtr;
{ assert gcAndMutatorTids(tid, mutatorTids); sweepPtr := memHi; }

yield procedure {:layer 95} InitSweepPtr({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool)
refines AtomicInitSweepPtr;
{
    call PrimitiveSetSweepPtr(memHi);
}

<-> action {:layer 96} AtomicReadSweepPtr({:linear "tid"} tid:Tid) returns(val:int)
{ assert tidHasLock(tid, lock); val := sweepPtr; }

yield procedure {:layer 95} ReadSweepPtr({:linear "tid"} tid:Tid) returns(val:int)
refines AtomicReadSweepPtr;
{
    call val := PrimitiveReadSweepPtr();
}

>-< action {:layer 96} AtomicSetSweepPtrLocked({:linear "tid"} tid:Tid, val: int)
modifies sweepPtr;
{ assert tid == GcTid && tidHasLock(tid, lock); sweepPtr := val; }

yield procedure {:layer 95} SetSweepPtrLocked({:linear "tid"} tid:Tid, val: int)
refines AtomicSetSweepPtrLocked;
{
    call PrimitiveSetSweepPtr(val);
}

>-< action {:layer 96} AtomicCollectorRootScanBarrierStartLocked({:linear "tid"} tid: Tid)
modifies rootScanOn;
{ assert tid == GcTid && tidHasLock(tid, lock); rootScanOn := true; }

yield procedure {:layer 95} CollectorRootScanBarrierStartLocked({:linear "tid"} tid: Tid)
refines AtomicCollectorRootScanBarrierStartLocked;
{
    call PrimitiveSetRootScanOn(true);
}

>-< action {:layer 96} AtomicCollectorRootScanBarrierEndLocked({:linear "tid"} tid: Tid)
modifies rootScanOn;
{ assert tid == GcTid && tidHasLock(tid, lock); rootScanOn := false; }

yield procedure {:layer 95} CollectorRootScanBarrierEndLocked({:linear "tid"} tid: Tid)
refines AtomicCollectorRootScanBarrierEndLocked;
{
    call PrimitiveSetRootScanOn(false);
}

-> action {:layer 96} AtomicMutatorReadBarrierOn({:linear "tid"} tid: Tid) returns (val:bool)
{ assert tidHasLock(tid, lock); val := rootScanOn; }

yield procedure {:layer 95} MutatorReadBarrierOn({:linear "tid"} tid: Tid) returns (val:bool)
refines AtomicMutatorReadBarrierOn;
{
    call val := PrimitiveReadRootScanOn();
}

<-> action {:layer 96,99} AtomicPollMutatorReadBarrierOn({:linear "tid"} tid: Tid) returns (val:bool)
{ }

yield procedure {:layer 95} PollMutatorReadBarrierOn({:linear "tid"} tid: Tid) returns (val:bool)
refines AtomicPollMutatorReadBarrierOn;
{
    call val := PrimitiveReadRootScanOn();
}

>-< action {:layer 96,99} AtomicInitRootScanBarrier({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool)
modifies rootScanBarrier;
{ assert gcAndMutatorTids(tid, mutatorTids); rootScanBarrier := numMutators; }

yield procedure {:layer 95} InitRootScanBarrier({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool)
refines AtomicInitRootScanBarrier;
{
    call PrimitiveSetRootScanBarrier(numMutators);
}

>-< action {:layer 96} AtomicCollectorRootScanBarrierRead({:linear "tid"} tid: Tid) returns (val:int)
{ assert tid == GcTid; val := rootScanBarrier; }

yield procedure {:layer 95} CollectorRootScanBarrierRead({:linear "tid"} tid: Tid) returns (val:int)
refines AtomicCollectorRootScanBarrierRead;
{
    call val := PrimitiveReadRootScanBarrier();
}

>-< action {:layer 96} AtomicAddRootScanBarrier({:linear "tid"} tid_left: Tid, val: int)
modifies rootScanBarrier;
{ assert mutatorTidLeft(tid_left) && tidHasLock(tid_left, lock); rootScanBarrier := rootScanBarrier + val; }

yield procedure {:layer 95} AddRootScanBarrier({:linear "tid"} tid_left: Tid, val: int)
refines AtomicAddRootScanBarrier;
{
    call PrimitiveAddRootScanBarrier(val);
}

-> action {:layer 96} AtomicMutatorsInRootScanBarrierAdd({:linear "tid"} tid_left: Tid, {:linear_in "tid"} tid_right: Tid)
modifies mutatorsInRootScanBarrier;
{
    assert tidHasLock(tid_left, lock) && mutatorTidRight(tid_right);
    mutatorsInRootScanBarrier[tid_right->i] := true;
}

yield procedure {:layer 95} MutatorsInRootScanBarrierAdd({:linear "tid"} tid_left: Tid, {:linear_in "tid"} tid_right: Tid)
refines AtomicMutatorsInRootScanBarrierAdd;
{
    call PrimitiveMutatorsInRootScanBarrierAdd(tid_right);
}

<-> action {:layer 96} AtomicMutatorsInRootScanBarrierRemove({:linear "tid"} tid_left: Tid) returns({:linear "tid"} tid_right: Tid)
modifies mutatorsInRootScanBarrier;
{
    assert tidHasLock(tid_left, lock) && !rootScanOn && mutatorTidLeft(tid_left) && mutatorsInRootScanBarrier[tid_left->i];
    mutatorsInRootScanBarrier[tid_left->i] := false;
    tid_right := Tid(tid_left->i, false, true);
}

yield procedure {:layer 95} MutatorsInRootScanBarrierRemove({:linear "tid"} tid_left: Tid) returns({:linear "tid"} tid_right: Tid)
refines AtomicMutatorsInRootScanBarrierRemove;
ensures {:layer 95} tid_left->i == tid_right->i;
ensures {:layer 95} tid_left->left && tid_right->right;
{
    call tid_right := PrimitiveMutatorsInRootScanBarrierRemove(tid_left);
}

<-> action {:layer 96,99} AtomicInitRoot({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool, x: int)
modifies root;
{ assert gcAndMutatorTids(tid, mutatorTids) && rootAddr(x); root[x] := 0; }

yield procedure {:layer 95} InitRoot({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool, x: int)
refines AtomicInitRoot;
{
    call PrimitiveWriteRoot(x, 0);
}

<- action {:layer 96,99} AtomicReadRootInRootScanBarrier({:linear "tid"} tid:Tid, x: idx) returns (val: int)
{ assert tid == GcTid && rootAddr(x) && rootScanOn && mutatorsInRootScanBarrier == Mutators; val := root[x]; }

yield procedure {:layer 95} ReadRootInRootScanBarrier({:linear "tid"} tid:Tid, x: idx) returns (val: int)
refines AtomicReadRootInRootScanBarrier;
{
    call val := PrimitiveReadRoot(x);
}

<-> action {:layer 96,99} AtomicWriteRoot({:linear "tid"} tid: Tid, i: idx, val: int)
modifies root;
{ assert mutatorTidWhole(tid) && rootAddr(i) && tidOwns(tid, i); root[i] := val; }

yield procedure {:layer 95} WriteRoot({:linear "tid"} tid: Tid, i: idx, val: int)
refines AtomicWriteRoot;
{
    call PrimitiveWriteRoot(i, val);
}

<-> action {:layer 96,99} AtomicReadRoot({:linear "tid"} tid: Tid, i: idx) returns (val: int)
{ assert mutatorTidWhole(tid) && rootAddr(i) && tidOwns(tid, i); val := root[i]; }

yield procedure {:layer 95} ReadRoot({:linear "tid"} tid: Tid, i: idx) returns (val: int)
refines AtomicReadRoot;
{
    call val := PrimitiveReadRoot(i);
}

<-> action {:layer 96,99} AtomicInitColor({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool, x: int)
modifies Color;
{ assert gcAndMutatorTids(tid, mutatorTids) && memAddr(x); Color[x] := UNALLOC(); }

yield procedure {:layer 95} InitColor({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool, x: int)
refines AtomicInitColor;
{
    call PrimitiveSetColor(x, UNALLOC());
}

<-> action {:layer 96} AtomicReadColorByCollector({:linear "tid"} tid:Tid, i: int) returns (val: int)
{ assert tid == GcTid && tidHasLock(tid, lock) && memAddr(i); val := Color[i]; }

yield procedure {:layer 95} ReadColorByCollector({:linear "tid"} tid:Tid, i: int) returns (val: int)
refines AtomicReadColorByCollector;
{
    call val := PrimitiveReadColor(i);
}

>-< action {:layer 96} AtomicReadColorByMutator1({:linear "tid"} tid:Tid, i: int) returns (val: int)
{ assert mutatorTidWhole(tid) && memAddr(i); }

yield procedure {:layer 95} ReadColorByMutator1({:linear "tid"} tid:Tid, i: int) returns (val: int)
refines AtomicReadColorByMutator1;
{
    call val := PrimitiveReadColor(i);
}

<-> action {:layer 96} AtomicReadColorByMutator2({:linear "tid"} tid:Tid, i: int) returns (val: int)
{ assert mutatorTidWhole(tid) && tidHasLock(tid, lock) && memAddr(i); val := Color[i]; }

yield procedure {:layer 95} ReadColorByMutator2({:linear "tid"} tid:Tid, i: int) returns (val: int)
refines AtomicReadColorByMutator2;
{
    call val := PrimitiveReadColor(i);
}

>-< action {:layer 96,98} AtomicReadColorByMutator3({:linear "tid"} tid:Tid, i: int) returns (val: int)
{
    assert mutatorTidWhole(tid) && memAddr(i) && MarkPhase(mutatorPhase[tid->i]);
    assume White(Color[i]) ==> White(val);
}

yield procedure {:layer 95} ReadColorByMutator3({:linear "tid"} tid:Tid, i: int) returns (val: int)
refines AtomicReadColorByMutator3;
{
    call val := PrimitiveReadColor(i);
}

<-> action {:layer 96} AtomicSetColor({:linear "tid"} tid:Tid, i: int, val: int)
modifies Color;
{ assert tidHasLock(tid, lock) && memAddr(i) && PhaseConsistent(collectorPhase, mutatorPhase) && !MarkPhase(collectorPhase); Color[i] := val; }

yield procedure {:layer 95} SetColor({:linear "tid"} tid:Tid, i: int, val: int)
refines AtomicSetColor;
{
    call PrimitiveSetColor(i, val);
}

<- action {:layer 96} AtomicSetColor2({:linear "tid"} tid:Tid, i: int, val: int)
modifies Color;
{
    assert tidHasLock(tid, lock) && memAddr(i);
    assert (MarkPhase(collectorPhase) || !PhaseConsistent(collectorPhase, mutatorPhase) ==> !White(val));
    Color[i] := val;
}

yield procedure {:layer 95} SetColor2({:linear "tid"} tid:Tid, i: int, val: int)
refines AtomicSetColor2;
{
    call PrimitiveSetColor(i, val);
}

>-< action {:layer 96} AtomicSetColor3({:linear "tid"} tid:Tid, i: int, val: int, o: obj)
modifies Color, toAbs;
{
    assert tidHasLock(tid, lock) && memAddr(i);
    assert White(val) ==> Unalloc(Color[i]);
    Color[i] := val;
    toAbs[i] := o;
}

yield procedure {:layer 95} SetColor3({:linear "tid"} tid:Tid, i: int, val: int, o: obj)
refines AtomicSetColor3;
{
    call PrimitiveSetColor(i, val);
    call SetToAbs2(i, o);
}

<-> action {:layer 96,99} AtomicInitToAbs({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool)
modifies toAbs;
{
    assert gcAndMutatorTids(tid, mutatorTids);
    toAbs := (lambda i:int :: if memAddr(i) then nil else Int(i));
}

yield procedure {:layer 95} InitToAbs({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool)
refines AtomicInitToAbs;
{
    call SetToAbs3();
}

-> action {:layer 96} AtomicLockAcquire({:linear "tid"} tid: Tid)
modifies lock;
{ assert tid->i != 0; assume lock == 0; lock := tid->i; }

yield procedure {:layer 95} LockAcquire({:linear "tid"} tid: Tid)
refines AtomicLockAcquire;
{
    var status:bool;
    while (true)
    invariant {:yields} true;
    {
        call status := PrimitiveLockCAS(tid->i);
        if (status)
        {
            return;
        }
    }
}

<- action {:layer 96} AtomicLockRelease({:linear "tid"} tid:Tid)
modifies lock;
{ assert tidHasLock(tid, lock); lock := 0; }

yield procedure {:layer 95} LockRelease({:linear "tid"} tid:Tid)
refines AtomicLockRelease;
{
    call PrimitiveLockZero();
}

action {:layer 96} GhostReadMem() returns (snapMem: [int][fld]int)
{
    snapMem := mem;
}

action {:layer 99} GhostReadColor99() returns (snapColor: [int]int)
{
    snapColor := Color;
}

action {:layer 100} GhostReadColor100() returns (snapColor: [int]int)
{
    snapColor := Color;
}

//////////////////////////////////////////////////////////////////////////////
// ATOMIC PRIMITIVES
//   The action specifications, linearity specifications, and requires/ensures below here are trusted.
//   (Note, though, that Boogie still verifies the mover types (atomic,left,right,both); these are not trusted.)
//////////////////////////////////////////////////////////////////////////////

<-> action {:layer 1,96} AtomicTidSplit({:linear_in "tid"} tid:Tid) returns({:linear "tid"} tid_left:Tid, {:linear "tid"} tid_right:Tid)
{ assert tid->left && tid->right; tid_left := Tid(tid->i, true, false); tid_right := Tid(tid->i, false, true); }
yield procedure {:layer 0} TidSplit({:linear_in "tid"} tid:Tid) returns({:linear "tid"} tid_left:Tid, {:linear "tid"} tid_right:Tid);
refines AtomicTidSplit;

<-> action {:layer 1,96} AtomicTidCombine({:linear_in "tid"} tid_left:Tid, {:linear_in "tid"} tid_right:Tid) returns({:linear "tid"} tid:Tid)
{ assert tid_left->i == tid_right->i && tid_left->left && tid_right->right; tid := Tid(tid_left->i, true, true); }
yield procedure {:layer 0} TidCombine({:linear_in "tid"} tid_left:Tid, {:linear_in "tid"} tid_right:Tid) returns({:linear "tid"} tid:Tid);
refines AtomicTidCombine;

<-> action {:layer 1,99} AtomicTidOutput({:linear_in "tid"} tid_in:Tid, {:linear_out "tid"} tid_out:Tid)
{ assert tid_in == tid_out; }
yield procedure {:layer 0} TidOutput({:linear_in "tid"} tid_in:Tid, {:linear_out "tid"} tid_out:Tid);
refines AtomicTidOutput;

>-< action {:layer 1,95} AtomicPrimitiveReadField(x: int, f: fld) returns (y: int)
{ assert memAddr(x) && fieldAddr(f); y := mem[x][f]; }
yield procedure {:layer 0} PrimitiveReadField(x: int, f: fld) returns (y: int);
refines AtomicPrimitiveReadField;

>-< action {:layer 1,95} AtomicPrimitiveWriteField(x: int, f: fld, y: int)
modifies mem;
{ assert memAddr(x) && fieldAddr(f); mem[x][f] := y; }
yield procedure {:layer 0} PrimitiveWriteField(x: int, f: fld, y: int);
refines AtomicPrimitiveWriteField;

-> action {:layer 1,99} AtomicPrimitiveFindFreePtrAbs() returns (o: obj)
modifies allocSet;
{ assume (memAddrAbs(o) && !allocSet[o] && o != nil); allocSet[o] := true; }
yield procedure {:layer 0} PrimitiveFindFreePtrAbs() returns (o: obj);
refines AtomicPrimitiveFindFreePtrAbs;

>-< action {:layer 1,95} AtomicPrimitiveReadMarkStackPtr() returns (val: int)
{ val := MarkStackPtr; }
yield procedure {:layer 0} PrimitiveReadMarkStackPtr() returns (val: int);
refines AtomicPrimitiveReadMarkStackPtr;

>-< action {:layer 1,95} AtomicPrimitiveSetMarkStackPtr(val: int)
modifies MarkStackPtr;
{ MarkStackPtr := val; }
yield procedure {:layer 0} PrimitiveSetMarkStackPtr(val: int);
refines AtomicPrimitiveSetMarkStackPtr;

>-< action {:layer 1,95} AtomicPrimitiveReadMarkStack(ptr: int) returns (val: int)
{ val := MarkStack[ptr]; }
yield procedure {:layer 0} PrimitiveReadMarkStack(ptr: int) returns (val: int);
refines AtomicPrimitiveReadMarkStack;

>-< action {:layer 1,95} AtomicPrimitiveWriteMarkStack(ptr: int, val: int)
modifies MarkStack;
{ MarkStack[ptr] := val; }
yield procedure {:layer 0} PrimitiveWriteMarkStack(ptr: int, val: int);
refines AtomicPrimitiveWriteMarkStack;

>-< action {:layer 1,95} AtomicPrimitiveReadCollectorPhase() returns (phase: int)
{ phase := collectorPhase; }
yield procedure {:layer 0} PrimitiveReadCollectorPhase() returns (phase: int);
refines AtomicPrimitiveReadCollectorPhase;

>-< action {:layer 1,95} AtomicPrimitiveSetCollectorPhase(phase:int)
modifies collectorPhase;
{ collectorPhase := phase; }
yield procedure {:layer 0} PrimitiveSetCollectorPhase(phase: int);
refines AtomicPrimitiveSetCollectorPhase;

>-< action {:layer 1,95} AtomicPrimitiveReadMutatorPhase(i: int) returns (phase: int)
{ phase := mutatorPhase[i]; }
yield procedure {:layer 0} PrimitiveReadMutatorPhase(i: int) returns (phase: int);
refines AtomicPrimitiveReadMutatorPhase;

>-< action {:layer 1,95} AtomicPrimitiveSetMutatorPhase(i: int, phase: int)
modifies mutatorPhase;
{ mutatorPhase[i] := phase; }
yield procedure {:layer 0} PrimitiveSetMutatorPhase(i: int, phase: int);
refines AtomicPrimitiveSetMutatorPhase;

>-< action {:layer 1,95} AtomicPrimitiveReadSweepPtr() returns(val: int)
{ val := sweepPtr; }
yield procedure {:layer 0} PrimitiveReadSweepPtr() returns(val: int);
refines AtomicPrimitiveReadSweepPtr;

>-< action {:layer 1,95} AtomicPrimitiveSetSweepPtr(val: int)
modifies sweepPtr;
{ sweepPtr := val; }
yield procedure {:layer 0} PrimitiveSetSweepPtr(val: int);
refines AtomicPrimitiveSetSweepPtr;

>-< action {:layer 1,95} AtomicPrimitiveReadRootScanOn() returns(val: bool)
{ val := rootScanOn; }
yield procedure {:layer 0} PrimitiveReadRootScanOn() returns(val: bool);
refines AtomicPrimitiveReadRootScanOn;

>-< action {:layer 1,95} AtomicPrimitiveSetRootScanOn(val: bool)
modifies rootScanOn;
{ rootScanOn := val; }
yield procedure {:layer 0} PrimitiveSetRootScanOn(val: bool);
refines AtomicPrimitiveSetRootScanOn;

>-< action {:layer 1,95} AtomicPrimitiveReadRootScanBarrier() returns(val: int)
{ val := rootScanBarrier; }
yield procedure {:layer 0} PrimitiveReadRootScanBarrier() returns(val: int);
refines AtomicPrimitiveReadRootScanBarrier;

>-< action {:layer 1,95} AtomicPrimitiveSetRootScanBarrier(val: int)
modifies rootScanBarrier;
{ rootScanBarrier := val; }
yield procedure {:layer 0} PrimitiveSetRootScanBarrier(val: int);
refines AtomicPrimitiveSetRootScanBarrier;

>-< action {:layer 1,95} AtomicPrimitiveAddRootScanBarrier(val: int)
modifies rootScanBarrier;
{ rootScanBarrier := rootScanBarrier + val; }
yield procedure {:layer 0} PrimitiveAddRootScanBarrier(val: int);
refines AtomicPrimitiveAddRootScanBarrier;

>-< action {:layer 1,95} AtomicPrimitiveMutatorsInRootScanBarrierAdd({:linear_in "tid"} tid_right: Tid)
modifies mutatorsInRootScanBarrier;
{ assert mutatorTidRight(tid_right); mutatorsInRootScanBarrier[tid_right->i] := true; }
yield procedure {:layer 0} PrimitiveMutatorsInRootScanBarrierAdd({:linear_in "tid"} tid_right: Tid);
refines AtomicPrimitiveMutatorsInRootScanBarrierAdd;

>-< action {:layer 1,95} AtomicPrimitiveMutatorsInRootScanBarrierRemove({:linear "tid"} tid_left: Tid) returns({:linear "tid"} tid_right: Tid)
modifies mutatorsInRootScanBarrier;
{ assert mutatorTidLeft(tid_left) && mutatorsInRootScanBarrier[tid_left->i]; mutatorsInRootScanBarrier[tid_left->i] := false; tid_right := Tid(tid_left->i, false, true); }
yield procedure {:layer 0} PrimitiveMutatorsInRootScanBarrierRemove({:linear "tid"} tid_left: Tid) returns({:linear "tid"} tid_right: Tid);
refines AtomicPrimitiveMutatorsInRootScanBarrierRemove;

>-< action {:layer 1,95} AtomicPrimitiveWriteRoot(i: idx, val: int)
modifies root;
{ assert rootAddr(i); root[i] := val; }
yield procedure {:layer 0} PrimitiveWriteRoot(i: idx, val: int);
refines AtomicPrimitiveWriteRoot;

>-< action {:layer 1,95} AtomicPrimitiveReadRoot(i: idx) returns (val: int)
{ assert rootAddr(i); val := root[i]; }
yield procedure {:layer 0} PrimitiveReadRoot(i: idx) returns (val: int);
refines AtomicPrimitiveReadRoot;

>-< action {:layer 1,95} AtomicPrimitiveReadColor(i: int) returns (val: int)
{ assert memAddr(i); val := Color[i]; }
yield procedure {:layer 0} PrimitiveReadColor(i: int) returns (val: int);
refines AtomicPrimitiveReadColor;

>-< action {:layer 1,95} AtomicPrimitiveSetColor(i: int, val: int)
modifies Color;
{ assert memAddr(i); Color[i] := val; }
yield procedure {:layer 0} PrimitiveSetColor(i: int, val: int);
refines AtomicPrimitiveSetColor;

>-< action {:layer 1,95} AtomicPrimitiveLockCAS(next: int) returns (status: bool)
modifies lock;
{
    assert next != 0;
    if (*) {
        assume lock == 0; lock := next; status := true;
    } else {
        status := false;
    }
}
yield procedure {:layer 0} PrimitiveLockCAS(next: int) returns (status: bool);
refines AtomicPrimitiveLockCAS;

>-< action {:layer 1,95} AtomicPrimitiveLockZero()
modifies lock;
{ lock := 0; }
yield procedure {:layer 0} PrimitiveLockZero();
refines AtomicPrimitiveLockZero;

action {:layer 99} SetMemAbs1(x: idx, f: fld, y: idx)
modifies memAbs;
{
    memAbs[rootAbs[x]][f] := rootAbs[y];
}

action {:layer 99} SetRootAbs1(x: idx, f: fld, y: idx)
modifies rootAbs;
{
    rootAbs[y] := memAbs[rootAbs[x]][f];
}

action {:layer 99} SetMemAbs2(absPtr: obj)
modifies memAbs;
{
    memAbs[absPtr] := (lambda z: int :: if (fieldAddr(z)) then absPtr else memAbs[absPtr][z]);
}

action {:layer 99} SetRootAbs2(y: idx, absPtr: obj)
modifies rootAbs;
{
    rootAbs[y] := absPtr;
}

action {:layer 95} SetToAbs1()
modifies toAbs;
{
    toAbs := (lambda x: int :: if memAddr(x) && White(Color[x]) then nil else toAbs[x]);
}

action {:layer 95} SetToAbs2(i: int, o: obj)
modifies toAbs;
{
    toAbs[i] := o;
}

action {:layer 95} SetToAbs3()
modifies toAbs;
{
    toAbs := (lambda i:int :: if memAddr(i) then nil else Int(i));
}
