//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Tid(i, ps) represents a linear thread id for thread number i, where i > 0 and ps = {Left(i), Right(i)}.
// Thread ids can be split into left and right fractions:
//   - For a whole thread id, both Left(i) and Right(i) are in ps.
//   - For a fraction, either Left(i) or Right(i) is in ps.
// In other words, Tid(i, { Left(i), Right(i) }) can be be split into Tid(i, { Left(i) }), Tid(i, { Right(i) }).
datatype Piece { Left(i:int), Right(i:int) }
datatype Tid { Tid(i:int, {:linear} ps: Set Piece) }

const numMutators: int;
axiom 0 < numMutators;
const GcTid: Tid;
axiom numMutators < GcTid->i;
axiom Set_Contains(GcTid->ps, Left(GcTid->i)) && Set_Contains(GcTid->ps, Right(GcTid->i));

function mutatorId(i: int) : bool { 1 <= i && i <= numMutators }
function mutatorTid(tid: Tid) : bool { mutatorId(tid->i) }
function mutatorTidLeft(tid: Tid) : bool { mutatorTid(tid) && Set_Contains(tid->ps, Left(tid->i)) }
function mutatorTidRight(tid: Tid) : bool { mutatorTid(tid) && Set_Contains(tid->ps, Right(tid->i)) }
function mutatorTidWhole(tid: Tid) : bool { mutatorTid(tid) && Set_Contains(tid->ps, Left(tid->i)) && Set_Contains(tid->ps, Right(tid->i)) }
function gcAndMutatorTids(tid: Tid, mutatorTids: Set Piece) : bool
{
    tid == GcTid && (forall i:int :: mutatorId(i) ==> Set_Contains(mutatorTids, Left(i)) && Set_Contains(mutatorTids, Right(i)))
}

const Mutators: Set Piece;
axiom Set_Size(Mutators) == numMutators;
axiom Mutators->val == (lambda x: Piece :: x is Right && 1 <= x->i && x->i <= numMutators);
axiom (forall X, Y: Set Piece :: Set_IsSubset(X, Y) ==> Set_Size(X) < Set_Size(Y) || X == Y);

function {:inline} RootScanBarrierInv(mutatorsInRootScanBarrier: Set Piece, rootScanBarrier: int) : bool
{
    Set_Size(mutatorsInRootScanBarrier) + rootScanBarrier == numMutators &&
    Set_IsSubset(mutatorsInRootScanBarrier, Mutators)
}

type idx = int;
type fld = int;
datatype obj { Null(), Obj(id:int), Int(i:int) }

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
var {:layer 99,101} rootAbs: [idx]obj;
var {:layer 99,101} allocSet: [obj]bool;
var {:layer 99,101} memAbs: [obj][fld]obj;

// Next layer
var {:layer 0,100} root: [idx]int;
var {:layer 0,100} mem: [int][fld]int;
var {:layer 95,100} toAbs: [int]obj;
var {:layer 0,100} Color: [int]int;
var {:layer 0,100} collectorPhase: int;
var {:layer 0,100} mutatorPhase: [int]int;
var {:layer 0,100} sweepPtr: int;

// Next layer
var {:layer 0,99} rootScanOn: bool;
var {:layer 0,99} rootScanBarrier: int;
var {:linear} {:layer 95,99} mutatorsInRootScanBarrier: Set Piece;
var {:layer 0,98} MarkStack: [int]int;
var {:layer 0,98} MarkStackPtr: int;

// Next layer
// Lock is used during allocation and GC.  To ensure good performance, it is not used for mutator reads and writes.
var {:layer 95,96} absLock: int; // 0 if unheld; thread number of holder if held
var {:layer 0,95} lock: bool; // false if unheld; true if held

function tidHasLock(tid:Tid, lock:int):bool { (tid == GcTid || mutatorTid(tid)) && lock == tid->i && Set_Contains(tid->ps, Left(tid->i)) }

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
axiom nil == Null();
axiom memAddrAbs(Null());
axiom (forall i:int :: memAddrAbs(Obj(i)));
axiom (forall i:int :: !memAddrAbs(Int(i)));

function owner(x: idx): int;
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

yield invariant {:layer 100} Yield_WriteField({:linear} tid:Tid, x: idx, y: idx);
invariant mutatorTidWhole(tid) && tidOwns(tid, x) && tidOwns(tid, y);
invariant memAddr(root[y]) && MarkPhase(mutatorPhase[tid->i]) ==> Gray(Color[root[y]]) || Black(Color[root[y]]);

yield invariant {:layer 100} Yield_Iso();
invariant Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);

yield invariant {:layer 100} Yield_GarbageCollect_100({:linear} tid:Tid);
invariant tid == GcTid;
invariant (forall x: int :: memAddr(x) ==> (toAbs[x] == nil <==> Unalloc(Color[x])));
invariant sweepPtr == memHi ==> (forall x: int :: memAddr(x) ==> !Black(Color[x]));
invariant sweepPtr == memLo ==>
            (forall x: int :: memAddr(x) ==> !Gray(Color[x])) &&
            (forall i: int :: rootAddr(i) && memAddr(root[i]) ==> Black(Color[root[i]])) &&
            (forall x: int, f: fld :: memAddr(x) && Black(Color[x]) && fieldAddr(f) && memAddr(mem[x][f]) ==> Black(Color[mem[x][f]]));

yield invariant {:layer 100} Yield_CollectorPhase_100({:linear} tid:Tid, tick_collectorPhase: int);
invariant tid == GcTid;
invariant tick_collectorPhase == collectorPhase;

yield invariant {:layer 100} Yield_SweepPtr_100({:linear} tid:Tid, tick_sweepPtr: int);
invariant tid == GcTid;
invariant tick_sweepPtr == sweepPtr;

yield invariant {:layer 100} Yield_MarkBegin({:linear} tid:Tid, tick_Color: [int]int);
invariant tid == GcTid;
invariant MarkPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase) && sweepPtr == memHi;
invariant (forall x: int :: memAddr(x) ==> (toAbs[x] == nil <==> Unalloc(Color[x])));
invariant (forall x: int :: memAddr(x) ==> !Black(Color[x]));
invariant (forall x: int :: memAddr(x) && !Unalloc(tick_Color[x]) ==> !Unalloc(Color[x]));
invariant (forall x: int :: memAddr(x) && !Unalloc(tick_Color[x]) && !White(tick_Color[x]) ==> !White(Color[x]));

yield invariant {:layer 100} Yield_Mark({:linear} tid:Tid, tick_Color: [int]int);
invariant tid == GcTid;
invariant MarkPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase) && sweepPtr == memLo;
invariant MarkInv(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
invariant (forall x: int :: memAddr(x) && !Unalloc(tick_Color[x]) ==> !Unalloc(Color[x]));
invariant (forall x: int :: memAddr(x) && !Unalloc(tick_Color[x]) && !White(tick_Color[x]) ==> !White(Color[x]));

yield invariant {:layer 100} Yield_MarkEnd({:linear} tid:Tid);
invariant tid == GcTid;
invariant MarkPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase) && sweepPtr == memLo;
invariant MarkInv(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
invariant (forall x: int :: memAddr(x) ==> !Gray(Color[x]));
invariant (forall i: int :: rootAddr(i) && memAddr(root[i]) ==> Black(Color[root[i]]));

yield invariant {:layer 100} Yield_MarkInnerLoopFieldIter({:linear} tid:Tid, fldIter: int, nodeProcessed: int);
invariant tid == GcTid;
invariant 0 <= fldIter && fldIter <= numFields;
invariant MarkPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase) && sweepPtr == memLo;
invariant MarkInv(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
invariant !Unalloc(Color[nodeProcessed]);
invariant (forall x: int :: 0 <= x && x < fldIter && memAddr(mem[nodeProcessed][x]) ==> !Unalloc(Color[mem[nodeProcessed][x]]) && !White(Color[mem[nodeProcessed][x]]));

yield invariant {:layer 100} Yield_SweepBegin({:linear} tid:Tid, isInit: bool, tick_Color: [int]int);
invariant tid == GcTid;
invariant SweepPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase);
invariant sweepPtr == memLo;
invariant !isInit ==> SweepInv(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
invariant isInit ==> SweepInvInit(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
invariant (forall i: int :: rootAddr(i) && memAddr(root[i]) ==> Black(Color[root[i]]));
invariant (forall x: int :: memAddr(x) && !Unalloc(tick_Color[x]) ==> tick_Color[x] == Color[x]);

yield invariant {:layer 100} Yield_SweepEnd({:linear} tid:Tid);
invariant tid == GcTid;
invariant SweepPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase);
invariant sweepPtr == memHi;
invariant SweepInv(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
invariant (forall x: int :: memAddr(x) ==> !Black(Color[x]));

yield invariant {:layer 100} Yield_Initialize_100({:linear} tid:Tid, {:linear} mutatorTids:Set Piece);
invariant gcAndMutatorTids(tid, mutatorTids);
invariant (forall x: idx :: rootAddr(x) ==> rootAbs[x] == Int(0));

yield procedure {:layer 100}
Initialize({:layer 95, 100} {:linear_in} tid:Tid, {:layer 95, 100} {:linear} mutatorTids:Set Piece)
requires {:layer 97,98,99} gcAndMutatorTids(tid, mutatorTids);
requires call Yield_Initialize_100(tid, mutatorTids);
requires call Yield_InitVars99(mutatorTids, Set_Empty(), old(rootScanBarrier));
requires call Yield_Lock();
ensures call Yield_Iso();
ensures call Yield_RootScanBarrierInv();
ensures call Yield_InitVars99(mutatorTids, Set_Empty(), numMutators);
{
    par InitVars99(tid, mutatorTids) | Yield_Lock();
    par InitVars100(tid, mutatorTids) | Yield_Lock();
    async call GarbageCollect(tid);
}

atomic action {:layer 101} AtomicAlloc({:linear} tid:Tid, i: int, y:idx)
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
Alloc({:layer 95, 100} {:linear} tid:Tid, i: int, y:idx)
refines AtomicAlloc;
requires {:layer 95,96,99,100} mutatorTidWhole(tid);
preserves call Yield_Iso();
requires call Yield_RootScanBarrierEnter(tid);
requires call Yield_RootScanBarrierInv();
preserves call Yield_Lock();
requires {:layer 96} tid->i == i;
{
    var ptr: int;
    var absPtr: obj;

    par TestRootScanBarrier(tid) | Yield_Lock();
    par Yield_Iso();
    call UpdateMutatorPhase(tid, i);
    par Yield_Iso();
    par ptr, absPtr := AllocRaw(tid, y) | Yield_Lock();
    assert {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
}

atomic action {:layer 101} AtomicWriteField({:linear} tid:Tid, i: int, x: idx, f: fld, y: idx) // x.f = y
modifies memAbs;
{ assert mutatorTidWhole(tid) && rootAddr(x) && tidOwns(tid, x) && fieldAddr(f) && rootAddr(y) && tidOwns(tid, y) && memAddrAbs(rootAbs[x]); memAbs[rootAbs[x]][f] := rootAbs[y]; }

yield procedure {:layer 100}
WriteField({:layer 95, 100} {:linear} tid:Tid, i: int, x: idx, f: fld, y: idx)
refines AtomicWriteField;
requires {:layer 98, 100} mutatorTidWhole(tid);
preserves call Yield_Iso();
preserves call Yield_Lock();
requires {:layer 95, 96, 99} tid->i == i;
{
    call WriteBarrier(tid, i, y);
    par Yield_Iso() | Yield_WriteField(tid, x, y);
    par WriteFieldRaw(tid, x, f, y) | Yield_Lock();
}

atomic action {:layer 101} AtomicReadField({:linear} tid:Tid, x: idx, f: fld, y: idx) // y = x.f
modifies rootAbs;
{ assert mutatorTidWhole(tid) && rootAddr(x) && tidOwns(tid, x) && fieldAddr(f) && rootAddr(y) && tidOwns(tid, y) && memAddrAbs(rootAbs[x]); rootAbs[y] := memAbs[rootAbs[x]][f]; }

yield procedure {:layer 100}
ReadField({:layer 95, 100} {:linear} tid:Tid, x: idx, f: fld, y: idx)
refines AtomicReadField;
preserves call Yield_Iso();
{
    call ReadFieldRaw(tid, x, f, y);
}

atomic action {:layer 101} AtomicEq({:linear} tid:Tid, x: idx, y:idx) returns (isEqual:bool)
{ assert mutatorTidWhole(tid) && rootAddr(x) && tidOwns(tid, x) && rootAddr(y) && tidOwns(tid, y); isEqual := rootAbs[x] == rootAbs[y]; }

yield procedure {:layer 100}
Eq({:layer 95, 100} {:linear} tid:Tid, x: idx, y:idx) returns (isEqual:bool)
refines AtomicEq;
preserves call Yield_Iso();
{
    call isEqual := EqRaw(tid, x, y);
}

yield procedure {:layer 100}
GarbageCollect({:layer 95, 100} {:linear} tid:Tid)
requires {:layer 97,98,99,100} tid == GcTid;
requires call Yield_Iso();
requires call Yield_MsWellFormed(tid, 0);
requires call Yield_RootScanBarrierInv();
requires call Yield_GarbageCollect_100(tid);
requires call Yield_CollectorPhase_100(tid, IDLE());
requires call Yield_SweepPtr_100(tid, memHi);
requires call Yield_Lock();
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
        invariant call Yield_Lock();
    {
        call nextPhase := HandshakeCollector(tid); // IDLE --> MARK
        par Yield_WaitForMutators(tid, collectorPhase, false, 0) |
            Yield_Iso() |
            Yield_MsWellFormed(tid, 0) |
            Yield_RootScanBarrierInv() |
            Yield_GarbageCollect_100(tid) |
            Yield_CollectorPhase_100(tid, collectorPhase) |
            Yield_SweepPtr_100(tid, sweepPtr);
        par WaitForMutators(tid, nextPhase) | Yield_Lock();
        call MarkOuterLoop(tid);
        call nextPhase := HandshakeCollector(tid); // MARK --> SWEEP
        par Yield_WaitForMutators(tid, collectorPhase, false, 0) |
            Yield_Iso() |
            Yield_MsWellFormed(tid, 0) |
            Yield_RootScanBarrierInv() |
            Yield_GarbageCollect_100(tid) |
            Yield_CollectorPhase_100(tid, collectorPhase) |
            Yield_SweepPtr_100(tid, sweepPtr);
        par WaitForMutators(tid, nextPhase) | Yield_Lock();
        call Sweep(tid);
        call nextPhase := HandshakeCollector(tid); // SWEEP --> IDLE
    }
}

yield procedure {:layer 100}
MarkOuterLoop({:layer 95, 100} {:linear} tid:Tid)
preserves call Yield_Iso();
requires call Yield_MarkBegin(tid, old(Color));
ensures call Yield_MarkEnd(tid);
preserves call Yield_MsWellFormed(tid, 0);
preserves call Yield_CollectorPhase_98(tid, old(collectorPhase));
preserves call Yield_RootScanBarrierInv();
preserves call Yield_Lock();
{
    var canStop: bool;

    call ResetSweepPtr(tid);
    while (true)
        invariant {:yields} true;
        invariant call Yield_Mark(tid, old(Color));
        invariant call Yield_MsWellFormed(tid, 0);
        invariant call Yield_CollectorPhase_98(tid, old(collectorPhase));
        invariant call Yield_RootScanBarrierInv();
        invariant call Yield_Lock();
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
MarkInnerLoop({:layer 95, 100} {:linear} tid:Tid)
preserves call Yield_Iso();
preserves call Yield_Mark(tid, old(Color));
preserves call Yield_MsWellFormed(tid, 0);
preserves call Yield_CollectorPhase_98(tid, old(collectorPhase));
preserves call Yield_RootScanBarrierInv();
preserves call Yield_Lock();
{
    var nodeProcessed:int;
    var fldIter: int;
    var isEmpty: bool;
    var child: int;

    while (true)
        invariant {:yields} true;
        invariant call Yield_Mark(tid, old(Color));
        invariant call Yield_MsWellFormed(tid, 0);
        invariant call Yield_CollectorPhase_98(tid, old(collectorPhase));
        invariant call Yield_RootScanBarrierInv();
        invariant call Yield_Lock();
    {
        call isEmpty, nodeProcessed := RemoveFromStack(tid);
        if (isEmpty) {
            break;
        }
        fldIter := 0;
        while (fldIter < numFields)
            invariant {:yields} true;
            invariant call Yield_Mark(tid, old(Color));
            invariant call Yield_MsWellFormed(tid, nodeProcessed);
            invariant call Yield_CollectorPhase_98(tid, old(collectorPhase));
            invariant call Yield_RootScanBarrierInv();
            invariant call Yield_MarkInnerLoopFieldIter(tid, fldIter, nodeProcessed);
            invariant call Yield_Lock();
        {
            par child := ReadFieldByCollector(tid, nodeProcessed, fldIter) | Yield_Lock();
            if (memAddr(child))
            {
                call InsertIntoSetIfWhiteByCollector(tid, nodeProcessed, child);
            }
            fldIter := fldIter + 1;
        }
        call SetColorToBlack(tid, nodeProcessed);
    }
}

yield procedure {:layer 100}
Sweep({:layer 95, 100} {:linear} tid:Tid)
requires {:layer 98,99,100} tid == GcTid;
preserves call Yield_Iso();
preserves call Yield_MsWellFormed(tid, 0);
preserves call Yield_RootScanBarrierInv();
requires call Yield_SweepBegin(tid, false, old(Color));
ensures call Yield_SweepEnd(tid);
preserves call Yield_Lock();
{
    var localSweepPtr: int;
    var {:layer 100} snapColor: [int]int;

    localSweepPtr := memLo;
    call ClearToAbsWhite(tid);
    par Yield_SweepBegin(tid, true, Color) | Yield_MsWellFormed(tid, 0) | Yield_RootScanBarrierInv() | Yield_Iso();

    call {:layer 100} snapColor := Copy(Color);
    while (localSweepPtr < memHi)
        invariant {:yields} {:layer 96} true;
        invariant {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
        invariant {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
        invariant {:layer 100} SweepPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase);
        invariant {:layer 100} localSweepPtr == sweepPtr && memLo <= sweepPtr && sweepPtr <= memHi;
        invariant {:layer 100} (forall i: int :: rootAddr(i) && memAddr(root[i]) ==> Black(snapColor[root[i]]));
        invariant {:layer 100} SweepInvInit(root, rootAbs, mem, memAbs, snapColor, toAbs, allocSet);
        invariant {:layer 100} (forall i:int:: memAddr(i) ==> if sweepPtr <= i then Color[i] == snapColor[i] else if Black(snapColor[i]) then White(Color[i]) else Unalloc(Color[i]));
        invariant call Yield_Lock();
    {
        call SweepNext(tid);
        localSweepPtr := localSweepPtr + 1;
    }
}

//////////////////////////////////////////////////////////////////////////////
// Layer 99
//////////////////////////////////////////////////////////////////////////////

yield invariant {:layer 99} Yield_CollectorPhase_99({:linear} tid:Tid, tick_collectorPhase: int);
invariant tid == GcTid;
invariant tick_collectorPhase == collectorPhase;

yield invariant {:layer 99} Yield_SweepPtr_99({:linear} tid:Tid, tick_sweepPtr: int);
invariant tid == GcTid;
invariant tick_sweepPtr == sweepPtr;

yield invariant {:layer 99} Yield_RootScanBarrierInv();
invariant RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);

yield invariant {:layer 99} Yield_InitVars99({:linear} mutatorTids:Set Piece, tick_mutatorsInRootScanBarrier: Set Piece, tick_rootScanBarrier: int);
invariant (forall i:int :: mutatorId(i) ==> Set_Contains(mutatorTids, Left(i)) && Set_Contains(mutatorTids, Right(i)));
invariant mutatorsInRootScanBarrier == tick_mutatorsInRootScanBarrier;
invariant rootScanBarrier == tick_rootScanBarrier;

yield invariant {:layer 99} Yield_RootScanOn({:linear} tid: Tid, tick_rootScanOn: bool);
invariant tid == GcTid;
invariant rootScanOn == tick_rootScanOn;

yield invariant {:layer 99} Yield_RootScanBarrierEnter({:linear} tid: Tid);
invariant mutatorTidWhole(tid);
invariant !Set_Contains(mutatorsInRootScanBarrier, Right(tid->i));

yield invariant {:layer 99} Yield_RootScanBarrierWait({:linear} tid: Tid);
invariant mutatorTidLeft(tid);
invariant Set_Contains(mutatorsInRootScanBarrier, Right(tid->i));

yield procedure {:layer 99}
InitVars99({:layer 95, 99} {:linear} tid:Tid, {:layer 95, 99} {:linear} mutatorTids:Set Piece)
requires {:layer 98,99} gcAndMutatorTids(tid, mutatorTids);
ensures call Yield_InitVars98(tid, mutatorTids, 0);
requires call Yield_InitVars99(mutatorTids, old(mutatorsInRootScanBarrier), old(rootScanBarrier));
ensures call Yield_InitVars99(mutatorTids, old(mutatorsInRootScanBarrier), numMutators);
{
    call InitRootScanBarrier(tid, mutatorTids);
    call InitVars98(tid, mutatorTids);
}

yield procedure {:layer 99}
TestRootScanBarrier({:layer 95, 99} {:linear} tid:Tid)
requires {:layer 95,96} mutatorTidWhole(tid);
requires call Yield_RootScanBarrierEnter(tid);
requires call Yield_RootScanBarrierInv();
preserves call Yield_Lock();
{
    var isRootScanOn: bool;
    var {:layer 95, 99} {:linear} tid_tmp: Tid;

    par isRootScanOn := PollMutatorReadBarrierOn(tid) | Yield_Lock();
    par Yield_RootScanBarrierInv() | Yield_RootScanBarrierEnter(tid) | Yield_97() | Yield_98();
    if (isRootScanOn)
    {
        assert{:layer 99} !Set_Contains(mutatorsInRootScanBarrier, Right(tid->i));
        call tid_tmp := MutatorRootScanBarrierEnter(tid);
        par Yield_RootScanBarrierInv() | Yield_RootScanBarrierWait(tid_tmp) | Yield_97() | Yield_98();
        assert{:layer 99} Set_Contains(mutatorsInRootScanBarrier, Right(tid_tmp->i));
        call tid_tmp := MutatorRootScanBarrierWait(tid_tmp);
        call {:layer 99} Move(tid_tmp, tid);
    }
}

atomic action {:layer 100} AtomicCanMarkStop({:linear} tid:Tid) returns (canStop: bool)
modifies Color;
{
    assert tid == GcTid;
    havoc Color;
    assume (forall u: int :: if memAddr(u) && White(old(Color)[u]) && (exists k: int :: rootAddr(k) && root[k] == u) then Color[u] == GRAY() else Color[u] == old(Color)[u]);
    canStop := (forall v: int :: memAddr(v) ==> !Gray(Color[v]));
}

yield procedure {:layer 99}
CanMarkStop({:layer 95, 99} {:linear} tid:Tid) returns (canStop: bool)
refines AtomicCanMarkStop;
requires {:layer 99} tid == GcTid;
preserves call Yield_MsWellFormed(tid, 0);
preserves call Yield_CollectorPhase_98(tid, old(collectorPhase));
preserves call Yield_RootScanBarrierInv();
preserves call Yield_Lock();
{
    var i: int;
    var o: int;
    var {:layer 99} snapColor: [int]int;

    call CollectorRootScanBarrierStart(tid);

    par Yield_MsWellFormed(tid, 0) | Yield_CollectorPhase_98(tid, old(collectorPhase)) | Yield_RootScanBarrierInv() | Yield_RootScanOn(tid, true) | Yield_97();

    call {:layer 99} snapColor := Copy(Color);
    par CollectorRootScanBarrierWait(tid) | Yield_Lock();

    i := 0;
    while (i < numRoots)
        invariant {:yields} {:layer 98} true;
        invariant call Yield_MsWellFormed(tid, 0);
        invariant call Yield_CollectorPhase_98(tid, old(collectorPhase));
        invariant {:layer 99} Mutators == mutatorsInRootScanBarrier && rootScanOn;
        invariant {:layer 99} 0 <= i && i <= numRoots;
        invariant {:layer 99} Color == (lambda u: int :: if memAddr(u) && White(snapColor[u]) && (exists k: int :: 0 <= k && k < i && root[k] == u) then GRAY() else snapColor[u]);
        invariant call Yield_Lock();
    {
        par o := ReadRootInRootScanBarrier(tid, i) | Yield_Lock();
        if (memAddr(o))
        {
            par InsertIntoSetIfWhiteInRootScanBarrier(tid, o) | Yield_Lock();
        }
        i := i + 1;
    }
    call canStop := NoGrayInRootScanBarrier(tid);
    call CollectorRootScanBarrierEnd(tid);
}

atomic action {:layer 100} AtomicWriteFieldRaw({:linear} tid:Tid, x: idx, f: fld, y: idx)
modifies memAbs,  mem;
{
    assert mutatorTidWhole(tid) && rootAddr(x) && tidOwns(tid, x) && fieldAddr(f) && rootAddr(y) && tidOwns(tid, y) && memAddr(root[x]) && toAbs[root[x]] != nil && memAddrAbs(rootAbs[x]);
    memAbs[rootAbs[x]][f] := rootAbs[y];
    mem[root[x]][f] := root[y];
}

yield procedure {:layer 99} WriteFieldRaw({:layer 95, 99} {:linear} tid:Tid, x: idx, f: fld, y: idx)
refines AtomicWriteFieldRaw;
requires {:layer 98} mutatorTidWhole(tid);
{
    var valx: int;
    var valy: int;

    call valx := ReadRoot(tid, x);
    call valy := ReadRoot(tid, y);
    call WriteFieldByMutator(tid, valx, f, valy);
    call {:layer 99} memAbs := Copy((var a, b := rootAbs[x], rootAbs[y]; memAbs[a := memAbs[a][f := b]]));
}

atomic action {:layer 100} AtomicReadFieldRaw({:linear} tid:Tid, x: idx, f: fld, y: idx)
modifies rootAbs, root;
{
    assert mutatorTidWhole(tid) && rootAddr(x) && tidOwns(tid, x) && fieldAddr(f) && rootAddr(y) && tidOwns(tid, y) && memAddr(root[x]) && toAbs[root[x]] != nil && memAddrAbs(rootAbs[x]);
    rootAbs[y] := memAbs[rootAbs[x]][f];
    root[y] := mem[root[x]][f];
}

yield procedure {:layer 99} ReadFieldRaw({:layer 95, 99} {:linear} tid:Tid, x: idx, f: fld, y: idx)
refines AtomicReadFieldRaw;
{
    var valx: int;
    var valy: int;

    call valx := ReadRoot(tid, x);
    call valy := ReadFieldByMutator(tid, valx, f);
    call WriteRoot(tid, y, valy);
    call {:layer 99} rootAbs := Copy((var a := rootAbs[x]; rootAbs[y := memAbs[a][f]]));
}

atomic action {:layer 100} AtomicEqRaw({:linear} tid:Tid, x: idx, y:idx) returns (isEqual:bool)
{ assert mutatorTidWhole(tid) && rootAddr(x) && tidOwns(tid, x) && rootAddr(y) && tidOwns(tid, y); isEqual := root[x] == root[y]; }

yield procedure {:layer 99} EqRaw({:layer 95, 99} {:linear} tid:Tid, x: idx, y:idx) returns (isEqual:bool)
refines AtomicEqRaw;
{
    var vx:int;
    var vy:int;

    call vx := ReadRoot(tid, x);
    call vy := ReadRoot(tid, y);
    isEqual := vx == vy;
}

atomic action {:layer 100} AtomicAllocRaw({:linear} tid:Tid, y:idx) returns (ptr: int, absPtr: obj)
modifies allocSet, rootAbs, root, toAbs, memAbs, Color, mem;
{
    assert mutatorTidWhole(tid) && rootAddr(y) && tidOwns(tid, y);
    assert (forall x: int, f: fld :: memAddr(x) && Unalloc(Color[x]) ==> toAbs[x] == nil);
    assume memAddr(ptr) && Unalloc(Color[ptr]);
    assume memAddrAbs(absPtr) && !allocSet[absPtr] && absPtr != nil;
    allocSet[absPtr] := true;
    rootAbs[y] := absPtr;
    root[y] := ptr;
    toAbs[ptr] := absPtr;
    memAbs[absPtr] := (lambda z: int :: if (fieldAddr(z)) then absPtr else memAbs[absPtr][z]);
    Color[ptr] := if sweepPtr <= ptr then BLACK() else WHITE();
    mem[ptr] := (lambda z: int :: if (fieldAddr(z)) then ptr else mem[ptr][z]);
}

yield procedure {:layer 99} AllocRaw({:layer 95, 99} {:linear} tid:Tid, y:idx) returns (ptr: int, absPtr: obj)
refines AtomicAllocRaw;
preserves call Yield_Lock();
{
    call {:layer 99} Assume(memAddrAbs(absPtr) && !allocSet[absPtr] && absPtr != nil);
    call {:layer 99} allocSet := Copy(allocSet[absPtr := true]);
    call ptr := FindFreePtr(tid, absPtr);
    par WriteRoot(tid, y, ptr) | Yield_Lock();
    call {:layer 99} memAbs := Copy(memAbs[absPtr := (lambda z: int :: if (fieldAddr(z)) then absPtr else memAbs[absPtr][z])]);
    call {:layer 99} rootAbs := Copy(rootAbs[y := absPtr]);
}

atomic action {:layer 100} AtomicWriteBarrier({:linear} tid:Tid, i: int, y:idx)
modifies Color;
{
    var val:int;
    assert mutatorTidWhole(tid) && rootAddr(y) && tidOwns(tid, y);
    val := root[y];
    if (MarkPhase(mutatorPhase[tid->i]) && memAddr(val) && White(Color[val])) {
        Color[val] := GRAY();
    }
}

yield procedure {:layer 99} WriteBarrier({:layer 95, 99} {:linear} tid:Tid, i: int, y:idx)
refines AtomicWriteBarrier;
requires {:layer 98} mutatorTidWhole(tid);
requires {:layer 96,99} tid->i == i;
preserves call Yield_Lock();
{
    var phase: int;
    var rootVal: int;

    par rootVal := ReadRoot(tid, y) | Yield_Lock();
    if (memAddr(rootVal))
    {
        par phase := ReadMutatorPhaseByMutator(tid, i) | Yield_Lock();
        if (MarkPhase(phase))
        {
            call InsertIntoSetIfWhiteByMutator(tid, rootVal);
        }
    }
}

//////////////////////////////////////////////////////////////////////////////
// Layer 98
//////////////////////////////////////////////////////////////////////////////

yield invariant {:layer 98} Yield_MsWellFormed({:linear} tid:Tid, nodePeeked: int);
invariant tid == GcTid;
invariant MsWellFormed(MarkStack, MarkStackPtr, Color, nodePeeked);

yield invariant {:layer 98} Yield_CollectorPhase_98({:linear} tid:Tid, tick_collectorPhase: int);
invariant tid == GcTid;
invariant tick_collectorPhase == collectorPhase;

yield invariant {:layer 98} Yield_SweepPtr_98({:linear} tid:Tid, tick_sweepPtr: int);
invariant tid == GcTid;
invariant tick_sweepPtr == sweepPtr;

yield invariant {:layer 98} Yield_MarkPhase({:linear} tid:Tid, ptr: int);
invariant mutatorTidWhole(tid);
invariant MarkPhase(mutatorPhase[tid->i]);

yield invariant {:layer 98} Yield_98();

yield invariant {:layer 98} Yield_InitVars98({:linear} tid:Tid, {:linear} mutatorTids:Set Piece, tick_MarkStackPtr: int);
invariant gcAndMutatorTids(tid, mutatorTids);
invariant MarkStackPtr == tick_MarkStackPtr;

yield procedure {:layer 98}
InitVars98({:layer 95, 98} {:linear} tid:Tid, {:layer 95, 98} {:linear} mutatorTids:Set Piece)
requires call Yield_InitVars98(tid, mutatorTids, old(MarkStackPtr));
ensures call Yield_InitVars98(tid, mutatorTids, 0);
{
    call InitMarkStackPtr(tid, mutatorTids);
}

atomic action {:layer 99} AtomicFindFreePtr({:linear} tid: Tid, absPtr: obj) returns (ptr: int)
modifies Color, toAbs, mem;
{
    assert mutatorTidWhole(tid);
    assert (forall x: int :: memAddr(x) && Unalloc(Color[x]) ==> toAbs[x] == nil);
    assume (memAddr(ptr) && Unalloc(Color[ptr]));
    Color[ptr] := if sweepPtr <= ptr then BLACK() else WHITE();
    toAbs[ptr] := absPtr;
    mem[ptr] := (lambda z: int :: if (fieldAddr(z)) then ptr else mem[ptr][z]);
}

yield procedure {:layer 98} FindFreePtr({:layer 95, 98} {:linear} tid: Tid, absPtr: obj) returns (ptr: int)
refines AtomicFindFreePtr;
preserves call Yield_Lock();
{
    var iter: int;
    var spaceFound: bool;

    spaceFound := false;
    while (true)
        invariant {:yields} true;
        invariant {:layer 98} !spaceFound;
        invariant call Yield_Lock();
    {
        iter := memLo;
        while (iter < memHi)
            invariant {:yields} true;
            invariant {:layer 98} !spaceFound;
            invariant {:layer 98} memLo <= iter && iter <= memHi;
            invariant call Yield_Lock();
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

atomic action {:layer 99} AtomicInsertIntoSetIfWhiteByMutator({:linear} tid:Tid, memLocal:int)
modifies Color;
{
    assert mutatorTidWhole(tid) && memAddr(memLocal) && MarkPhase(mutatorPhase[tid->i]);
    if (White(Color[memLocal])) {
        Color[memLocal] := GRAY();
    }
}

yield procedure {:layer 98}
InsertIntoSetIfWhiteByMutator({:layer 95, 98} {:linear} tid:Tid, memLocal:int)
refines AtomicInsertIntoSetIfWhiteByMutator;
preserves call Yield_MarkPhase(tid, memLocal);
preserves call Yield_Lock();
{
    var color:int;

    par color := ReadColorByMutator3(tid, memLocal) | Yield_Lock();
    if (!White(color))
    {
        return;
    }

    par Yield_97() | Yield_MarkPhase(tid, memLocal);

    call MsPushByMutator(tid, memLocal);
    assert {:layer 98} MST(MarkStackPtr-1);
}

left action {:layer 99} AtomicNoGrayInRootScanBarrier({:linear} tid:Tid) returns (noGray: bool)
{
    assert tid == GcTid && rootScanOn && mutatorsInRootScanBarrier == Mutators;
    noGray := (forall i: int :: memAddr(i) ==> !Gray(Color[i]));
}

yield procedure {:layer 98}
NoGrayInRootScanBarrier({:layer 95, 98} {:linear} tid:Tid) returns (noGray: bool)
refines AtomicNoGrayInRootScanBarrier;
preserves call Yield_MsWellFormed(tid, 0);
preserves call Yield_CollectorPhase_98(tid, old(collectorPhase));
preserves call Yield_Lock();
{
    call noGray := MsIsEmpty(tid);
    assert {:layer 98} noGray || MST(0);
}

left action {:layer 99} AtomicInsertIntoSetIfWhiteInRootScanBarrier({:linear} tid:Tid, memLocal:int)
modifies Color;
{
    assert tid == GcTid && rootScanOn && mutatorsInRootScanBarrier == Mutators && memAddr(memLocal);
    if (White(Color[memLocal])) {
        Color[memLocal] := GRAY();
    }
}

yield procedure {:layer 98}
InsertIntoSetIfWhiteInRootScanBarrier({:layer 95, 98} {:linear} tid:Tid, memLocal:int)
refines AtomicInsertIntoSetIfWhiteInRootScanBarrier;
preserves call Yield_MsWellFormed(tid, 0);
preserves call Yield_CollectorPhase_98(tid, old(collectorPhase));
preserves call Yield_Lock();
{
    call MsPushByCollector(tid, memLocal);
    assert {:layer 98} MST(MarkStackPtr-1);
}

left action {:layer 99,100} AtomicInsertIntoSetIfWhiteByCollector({:linear} tid:Tid, parent: int, child:int)
modifies Color;
{
    assert tid == GcTid;
    assert MarkPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase) && sweepPtr == memLo && memAddr(child);
    if (White(Color[child])) {
        Color[child] := GRAY();
    }
}

yield procedure {:layer 98}
InsertIntoSetIfWhiteByCollector({:layer 95, 98} {:linear} tid:Tid, parent: int, child:int)
refines AtomicInsertIntoSetIfWhiteByCollector;
requires {:layer 98} memAddr(parent) && memAddr(child);
preserves call Yield_MsWellFormed(tid, parent);
preserves call Yield_CollectorPhase_98(tid, old(collectorPhase));
preserves call Yield_Lock();
{
    call MsPushByCollector(tid, child);
    assert {:layer 98} MST(MarkStackPtr-1);
}

right action {:layer 99,100} AtomicRemoveFromStack({:linear} tid:Tid) returns (isEmpty: bool, val:int)
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
RemoveFromStack({:layer 95, 98} {:linear} tid:Tid) returns (isEmpty: bool, val:int)
refines AtomicRemoveFromStack;
requires call Yield_MsWellFormed(tid, 0);
ensures call Yield_MsWellFormed(tid, if isEmpty then 0 else val);
preserves call Yield_CollectorPhase_98(tid, old(collectorPhase));
preserves call Yield_Lock();
{
    assert {:layer 98} MST(MarkStackPtr - 1);
    call isEmpty, val := MsPop(tid);
}

//////////////////////////////////////////////////////////////////////////////
// Layer 97
//////////////////////////////////////////////////////////////////////////////

yield invariant {:layer 97} Yield_97();

yield invariant {:layer 97} Yield_WaitForMutators({:linear} tid:Tid, nextPhase: int, done: bool, i: int);
invariant tid == GcTid;
invariant nextPhase == collectorPhase;
invariant done ==> (forall j:int:: 1 <= j && j < i ==> nextPhase == mutatorPhase[j]);

atomic action {:layer 98,100} AtomicWaitForMutators({:linear} tid:Tid, nextPhase: int)
{
    assert tid == GcTid;
    assume (forall j:int:: mutatorId(j) ==> nextPhase == mutatorPhase[j]);
}

yield procedure {:layer 97}
WaitForMutators({:layer 95, 97} {:linear} tid:Tid, nextPhase: int)
refines AtomicWaitForMutators;
requires call Yield_WaitForMutators(tid, nextPhase, false, 0);
{
    var done: bool;
    var i: int;
    var mutatorPhaseLocal: int;

    done := false;
    call Yield_WaitForMutators(tid, nextPhase, done, 1);
    while (!done)
        invariant {:yields} true;
        invariant call Yield_WaitForMutators(tid, nextPhase, done, numMutators+1);
    {
        done := true;
        i := 1;
        call Yield_WaitForMutators(tid, nextPhase, done, i);
        while (i <= numMutators)
            invariant {:yields} true;
            invariant call Yield_WaitForMutators(tid, nextPhase, done, i);
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

atomic action {:layer 97,100} AtomicInitVars100({:linear} tid:Tid, {:linear} mutatorTids:Set Piece)
modifies mutatorPhase, root, toAbs, Color, mem, collectorPhase, sweepPtr;
{
    assert tid == GcTid;
    assert (forall i:int :: mutatorId(i) ==> Set_Contains(mutatorTids, Left(i)) && Set_Contains(mutatorTids, Right(i)));
    havoc mem, root, Color, mutatorPhase;
    assume (forall x: int, f: fld :: memAddr(x) && fieldAddr(f) ==> mem[x][f] == x);
    assume (forall x: idx :: rootAddr(x) ==> root[x] == 0);
    assume (forall i:int :: memAddr(i) ==> Color[i] == UNALLOC());
    assume (forall i:int :: mutatorId(i) ==> mutatorPhase[i] == IDLE());
    toAbs := (lambda i:int :: if memAddr(i) then nil else Int(i));
    collectorPhase := IDLE();
    sweepPtr := memHi;
}

yield procedure {:layer 96} InitVars100({:layer 95, 96} {:linear} tid:Tid, {:layer 95, 96} {:linear} mutatorTids:Set Piece)
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

atomic action {:layer 97,100} AtomicSetColorToBlack({:linear} tid:Tid, scannedLocal:int)
modifies Color;
{
    assert MarkPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase);
    assert tid == GcTid;
    assert memAddr(scannedLocal);
    Color[scannedLocal] := BLACK();
}

yield procedure {:layer 96} SetColorToBlack({:layer 95, 96} {:linear} tid:Tid, scannedLocal:int)
refines AtomicSetColorToBlack;
preserves call Yield_Lock();
{
    call LockAcquire(tid);
    par SetColorInMarkPhase(tid, scannedLocal, BLACK()) | Yield_Lock();
    call LockRelease(tid);
}

atomic action {:layer 97,98} AtomicMsPushByCollector({:linear} tid: Tid, val: int)
modifies Color, MarkStack, MarkStackPtr;
{
    assert memAddr(val) && tid == GcTid;
    if (White(Color[val])) {
        Color[val] := GRAY();
        MarkStack[MarkStackPtr] := val;
        MarkStackPtr := MarkStackPtr + 1;
    }
}

yield procedure {:layer 96} MsPushByCollector({:layer 95, 96} {:linear} tid: Tid, val: int)
refines AtomicMsPushByCollector;
preserves call Yield_Lock();
{
    var color:int;
    var stack:int;

    call LockAcquire(tid);
    par color := ReadColorByCollector(tid, val) | Yield_Lock();
    if (White(color))
    {
        par SetColorInMarkPhase(tid, val, GRAY()) | Yield_Lock();
        par stack := ReadMarkStackPtr(tid) | Yield_Lock();
        par WriteMarkStack(tid, stack, val) | Yield_Lock();
        stack := stack + 1;
        par SetMarkStackPtr(tid, stack) | Yield_Lock();
    }
    call LockRelease(tid);
}

atomic action {:layer 97,98} AtomicMsPushByMutator({:linear} tid: Tid, val: int)
modifies Color, MarkStack, MarkStackPtr;
{
    assert memAddr(val) && mutatorTidWhole(tid) && MarkPhase(mutatorPhase[tid->i]);
    if (White(Color[val])) {
        Color[val] := GRAY();
        MarkStack[MarkStackPtr] := val;
        MarkStackPtr := MarkStackPtr + 1;
    }
}

yield procedure {:layer 96} MsPushByMutator({:layer 95, 96} {:linear} tid: Tid, val: int)
refines AtomicMsPushByMutator;
preserves call Yield_Lock();
{
    var color:int;
    var stack:int;

    call LockAcquire(tid);
    par color := ReadColorByMutator2(tid, val) | Yield_Lock();
    if (White(color))
    {
        par SetColorInMarkPhase(tid, val, GRAY()) | Yield_Lock();
        par stack := ReadMarkStackPtr(tid) | Yield_Lock();
        par WriteMarkStack(tid, stack, val) | Yield_Lock();
        stack := stack + 1;
        par SetMarkStackPtr(tid, stack) | Yield_Lock();
    }
    call LockRelease(tid);
}

atomic action {:layer 97,98} AtomicMsPop({:linear} tid:Tid) returns (isEmpty: bool, val:int)
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

yield procedure {:layer 96} MsPop({:layer 95, 96} {:linear} tid:Tid) returns (isEmpty: bool, val:int)
refines AtomicMsPop;
preserves call Yield_Lock();
{
    var stack:int;

    call LockAcquire(tid);
    par stack := ReadMarkStackPtr(tid) | Yield_Lock();
    if (stack > 0)
    {
        stack := stack - 1;
        par SetMarkStackPtr(tid, stack) | Yield_Lock();
        par val := ReadMarkStack(tid, stack) | Yield_Lock();
        isEmpty := false;
    }
    else
    {
        val := 0;
        isEmpty := true;
    }
    call LockRelease(tid);
}

atomic action {:layer 97,98} AtomicMsIsEmpty({:linear} tid: Tid) returns (isEmpty: bool)
{ assert tid == GcTid; isEmpty := MarkStackPtr == 0; }

yield procedure {:layer 96} MsIsEmpty({:layer 95, 96} {:linear} tid: Tid) returns (isEmpty: bool)
refines AtomicMsIsEmpty;
preserves call Yield_Lock();
{
    var v:int;

    call LockAcquire(tid);
    par v := ReadMarkStackPtr(tid) | Yield_Lock();
    isEmpty := v == 0;
    call LockRelease(tid);
}

atomic action {:layer 97,100} AtomicResetSweepPtr({:linear} tid:Tid)
modifies sweepPtr;
{ assert tid == GcTid; sweepPtr := memLo; }

yield procedure {:layer 96} ResetSweepPtr({:layer 95, 96} {:linear} tid:Tid)
refines AtomicResetSweepPtr;
preserves call Yield_Lock();
{
    call LockAcquire(tid);
    par SetSweepPtrLocked(tid, memLo) | Yield_Lock();
    call LockRelease(tid);
}

left action {:layer 97,100} AtomicSweepNext({:linear} tid:Tid)
modifies Color, sweepPtr;
{
    assert SweepPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase);
    assert !Gray(Color[sweepPtr]);
    assert tid == GcTid;
    assert memAddr(sweepPtr);
    Color[sweepPtr] := if White(Color[sweepPtr]) then UNALLOC() else if Black(Color[sweepPtr]) then WHITE() else Color[sweepPtr];
    sweepPtr := sweepPtr + 1;
}

yield procedure {:layer 96} SweepNext({:layer 95, 96} {:linear} tid:Tid)
refines AtomicSweepNext;
preserves call Yield_Lock();
{
    var color:int;
    var sweep:int;

    call LockAcquire(tid);
    par sweep := ReadSweepPtr(tid) | Yield_Lock();
    par color := ReadColorByCollector(tid, sweep) | Yield_Lock();
    color := if White(color) then UNALLOC() else if Black(color) then WHITE() else color;
    par SetColor(tid, sweep, color) | Yield_Lock();
    sweep := sweep + 1;
    par SetSweepPtrLocked(tid, sweep) | Yield_Lock();
    call LockRelease(tid);
}

atomic action {:layer 97,100} AtomicHandshakeCollector({:linear} tid:Tid) returns (nextPhase: int)
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

yield procedure {:layer 96} HandshakeCollector({:layer 95, 96} {:linear} tid:Tid) returns (nextPhase: int)
refines AtomicHandshakeCollector;
preserves call Yield_Lock();
{
    var phase:int;

    call LockAcquire(tid);
    par phase := ReadCollectorPhase(tid) | Yield_Lock();
    nextPhase := if IdlePhase(phase) then MARK() else if MarkPhase(phase) then SWEEP() else IDLE();
    par SetCollectorPhase(tid, nextPhase) | Yield_Lock();
    call LockRelease(tid);
}

atomic action {:layer 97,100} AtomicUpdateMutatorPhase({:linear} tid: Tid, i: int)
modifies mutatorPhase;
{ assert mutatorTidWhole(tid); mutatorPhase[tid->i] := collectorPhase; }

yield procedure {:layer 96} UpdateMutatorPhase({:layer 95, 96} {:linear} tid: Tid, i: int)
refines AtomicUpdateMutatorPhase;
preserves call Yield_Lock();
requires {:layer 96} tid->i == i;
{
    var p:int;

    call LockAcquire(tid);
    par p := ReadCollectorPhaseLocked(tid) | Yield_Lock();
    par SetMutatorPhaseLocked(tid, i, p) | Yield_Lock();
    call LockRelease(tid);
}

atomic action {:layer 97,99} AtomicCollectorRootScanBarrierStart({:linear} tid: Tid)
modifies rootScanOn;
{ assert tid == GcTid; rootScanOn := true; }

yield procedure {:layer 96} CollectorRootScanBarrierStart({:layer 95, 96} {:linear} tid: Tid)
refines AtomicCollectorRootScanBarrierStart;
preserves call Yield_Lock();
{
    call LockAcquire(tid);
    par CollectorRootScanBarrierStartLocked(tid) | Yield_Lock();
    call LockRelease(tid);
}

left action {:layer 97,99} AtomicCollectorRootScanBarrierEnd({:linear} tid: Tid)
modifies rootScanOn;
{ assert tid == GcTid; rootScanOn := false; }

yield procedure {:layer 96} CollectorRootScanBarrierEnd({:layer 95, 96} {:linear} tid: Tid)
refines AtomicCollectorRootScanBarrierEnd;
preserves call Yield_Lock();
{
    call LockAcquire(tid);
    par CollectorRootScanBarrierEndLocked(tid) | Yield_Lock();
    call LockRelease(tid);
}

atomic action {:layer 97,99} AtomicCollectorRootScanBarrierWait({:linear} tid: Tid)
{ assert tid == GcTid; assume rootScanBarrier == 0; }

yield procedure {:layer 96} CollectorRootScanBarrierWait({:layer 95, 96} {:linear} tid: Tid)
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

atomic action {:layer 97,99} AtomicMutatorRootScanBarrierEnter({:linear_in} tid: Tid) returns({:linear} tid_left: Tid)
modifies rootScanBarrier, mutatorsInRootScanBarrier;
{
    var {:linear} p: One Piece;
    assert mutatorTidWhole(tid);
    rootScanBarrier := rootScanBarrier - 1;
    tid_left := tid;
    call p := One_Get(tid_left->ps, Right(tid_left->i));
    call One_Put(mutatorsInRootScanBarrier, p);
}

yield procedure {:layer 96} MutatorRootScanBarrierEnter({:layer 95, 96} {:linear_in} tid: Tid) returns({:layer 95, 96} {:linear} tid_left: Tid)
refines AtomicMutatorRootScanBarrierEnter;
requires {:layer 95} mutatorTidWhole(tid);
ensures {:layer 95,96} mutatorTidLeft(tid_left);
preserves call Yield_Lock();
{
    var {:layer 95, 96} {:linear} tid_right: Tid;

    call {:layer 95, 96} tid_left, tid_right := TidSplit(tid);
    call LockAcquire(tid_left);
    par MutatorsInRootScanBarrierAdd(tid_left, tid_right) | Yield_Lock();
    par AddRootScanBarrier(tid_left, -1) | Yield_Lock();
    call LockRelease(tid_left);
}

atomic action {:layer 97,99} AtomicMutatorRootScanBarrierWait({:linear_in} tid_left: Tid) returns({:linear} tid: Tid)
modifies rootScanBarrier, mutatorsInRootScanBarrier;
{
    var {:linear} p: One Piece; 
    assert mutatorTidLeft(tid_left) && Set_Contains(mutatorsInRootScanBarrier, Right(tid_left->i));
    assume !rootScanOn;
    rootScanBarrier := rootScanBarrier + 1;
    call p := One_Get(mutatorsInRootScanBarrier, Right(tid_left->i));
    tid := tid_left;
    call One_Put(tid->ps, p);
}

yield procedure {:layer 96} MutatorRootScanBarrierWait({:layer 95, 96} {:linear_in} tid_left: Tid) returns({:layer 95, 96} {:linear} tid: Tid)
refines AtomicMutatorRootScanBarrierWait;
requires {:layer 95,96} mutatorTidLeft(tid_left);
ensures {:layer 95,96} tid->i == tid_left->i;
ensures {:layer 95,96} mutatorTidWhole(tid);
preserves call Yield_Lock();
{
    var {:layer 95, 96} {:linear} tid_right: Tid;
    var b: bool;

    loop:
        assert {:yields} {:layer 96} true;
        call Yield_Lock();
        call LockAcquire(tid_left);
        par b := MutatorReadBarrierOn(tid_left) | Yield_Lock();
        if (!b)
        {
            par AddRootScanBarrier(tid_left, 1) | Yield_Lock();
            par tid_right := MutatorsInRootScanBarrierRemove(tid_left) | Yield_Lock();
            call LockRelease(tid_left);
            call {:layer 95, 96} tid := TidCombine(tid_left, tid_right);
            return;
        }
        call LockRelease(tid_left);
        goto loop;
}

atomic action {:layer 97,98} AtomicAllocIfPtrFree({:linear} tid:Tid, ptr:int, absPtr:obj) returns (spaceFound:bool)
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

yield procedure {:layer 96} AllocIfPtrFree({:layer 95, 96} {:linear} tid:Tid, ptr:int, absPtr:obj) returns (spaceFound:bool)
refines AtomicAllocIfPtrFree;
preserves call Yield_Lock();
{
    var color:int;
    var sweep:int;
    var t:[int]obj;
    var fldIter:fld;
    var {:layer 96} snapMem: [int][fld]int;

    par color := ReadColorByMutator1(tid, ptr) | Yield_Lock();
    if (Unalloc(color))
    {
        call Yield_96();
        call LockAcquire(tid);
        par color := ReadColorByMutator2(tid, ptr) | Yield_Lock();
        if (Unalloc(color))
        {
            spaceFound := true;
            par sweep := ReadSweepPtr(tid) | Yield_Lock();
            if (sweep <= ptr)
            {
                color := BLACK();
            }
            else
            {
                color := WHITE();
            }

            call {:layer 96} snapMem := Copy(mem);
            fldIter := 0;
            while (fldIter < numFields)
                invariant {:yields} {:layer 95} true;
                invariant {:layer 96} 0 <= fldIter && fldIter <= numFields;
                invariant {:layer 96} mem == snapMem[ptr := (lambda z: int :: if (0 <= z && z < fldIter) then ptr else snapMem[ptr][z])];
                invariant call Yield_Lock();
            {
                par InitializeFieldInAlloc(tid, ptr, fldIter) | Yield_Lock();
                fldIter := fldIter + 1;
            }

            par SetColorInAlloc(tid, ptr, color, absPtr) | Yield_Lock();
            call LockRelease(tid);
            return;
        }
        call LockRelease(tid);
    }
    spaceFound := false;
}

atomic action {:layer 97,100} AtomicIsWhiteByCollector({:linear} tid:Tid, i: int) returns (isWhite: bool)
{ assert tid == GcTid && memAddr(i); isWhite := White(Color[i]); }

yield procedure {:layer 96} IsWhiteByCollector({:layer 95, 96} {:linear} tid:Tid, i: int) returns (isWhite: bool)
refines AtomicIsWhiteByCollector;
preserves call Yield_Lock();
{
    var v:int;

    call LockAcquire(tid);
    par v := ReadColorByCollector(tid, i) | Yield_Lock();
    isWhite := White(v);
    call LockRelease(tid);
}

atomic action {:layer 97,100} AtomicClearToAbsWhite({:linear} tid:Tid)
modifies toAbs;
{ assert tid == GcTid; toAbs := (lambda x: int :: if memAddr(x) && White(Color[x]) then nil else toAbs[x]); }

yield procedure {:layer 96} ClearToAbsWhite({:layer 95, 96} {:linear} tid:Tid)
refines AtomicClearToAbsWhite;
preserves call Yield_Lock();
{
    call LockAcquire(tid);
    par LockedClearToAbsWhite(tid) | Yield_Lock();
    call LockRelease(tid);
}

yield invariant {:layer 96} Yield_96();

//////////////////////////////////////////////////////////////////////////////
// Layer 95
//////////////////////////////////////////////////////////////////////////////

atomic action {:layer 96} AtomicLockedClearToAbsWhite({:linear} tid:Tid)
modifies toAbs;
{ assert tid == GcTid && tidHasLock(tid, absLock); toAbs := (lambda x: int :: if memAddr(x) && White(Color[x]) then nil else toAbs[x]); }

yield procedure {:layer 95} LockedClearToAbsWhite({:layer 95} {:linear} tid:Tid)
refines AtomicLockedClearToAbsWhite;
{
    call {:layer 95} toAbs := Copy((lambda x: int :: if memAddr(x) && White(Color[x]) then nil else toAbs[x]));
}

both action {:layer 96,99} AtomicInitField({:linear} tid:Tid, {:linear} mutatorTids:Set Piece, x: int, f: int)
modifies mem;
{ assert gcAndMutatorTids(tid, mutatorTids) && memAddr(x) && fieldAddr(f); mem[x][f] := x; }

yield procedure {:layer 95} InitField({:layer 95} {:linear} tid:Tid, {:layer 95} {:linear} mutatorTids:Set Piece, x: int, f: int)
refines AtomicInitField;
{
    call PrimitiveWriteField(x, f, x);
}

atomic action {:layer 96,100} AtomicReadFieldByCollector({:linear} tid:Tid, x:int, f: fld) returns (y: int)
{ assert tid == GcTid && memAddr(x) && fieldAddr(f) && toAbs[x] != nil; y := mem[x][f]; }

yield procedure {:layer 95} ReadFieldByCollector({:layer 95} {:linear} tid:Tid, x:int, f: fld) returns (y: int)
refines AtomicReadFieldByCollector;
{
    call y := PrimitiveReadField(x, f);
}

atomic action {:layer 96,99} AtomicReadFieldByMutator({:linear} tid:Tid, x: int, f: fld) returns (y: int)
{ assert mutatorTidWhole(tid) && memAddr(x) && fieldAddr(f) && toAbs[x] != nil; y := mem[x][f]; }

yield procedure {:layer 95} ReadFieldByMutator({:layer 95} {:linear} tid:Tid, x: int, f: fld) returns (y: int)
refines AtomicReadFieldByMutator;
{
    call y := PrimitiveReadField(x, f);
}

atomic action {:layer 96,99} AtomicWriteFieldByMutator({:linear} tid:Tid, x: int, f: fld, y: int)
modifies mem;
{ assert mutatorTidWhole(tid) && memAddr(x) && fieldAddr(f) && toAbs[x] != nil; mem[x][f] := y; }

yield procedure {:layer 95} WriteFieldByMutator({:layer 95} {:linear} tid:Tid, x: int, f: fld, y: int)
refines AtomicWriteFieldByMutator;
{
    call PrimitiveWriteField(x, f, y);
}

right action {:layer 96} AtomicInitializeFieldInAlloc({:linear} tid: Tid, ptr: int, fld: int)
modifies mem;
{ assert mutatorTidWhole(tid) && tidHasLock(tid, absLock) && memAddr(ptr) && fieldAddr(fld) && toAbs[ptr] == nil; mem[ptr][fld] := ptr; }

yield procedure {:layer 95} InitializeFieldInAlloc({:layer 95} {:linear} tid: Tid, ptr: int, fld: int)
refines AtomicInitializeFieldInAlloc;
{
    call PrimitiveWriteField(ptr, fld, ptr);
}

both action {:layer 96} AtomicReadMarkStackPtr({:linear} tid:Tid) returns (val: int)
{ assert tidHasLock(tid, absLock); val := MarkStackPtr; }

yield procedure {:layer 95} ReadMarkStackPtr({:layer 95} {:linear} tid:Tid) returns (val: int)
refines AtomicReadMarkStackPtr;
{
    call val := PrimitiveReadMarkStackPtr();
}

atomic action {:layer 96,98} AtomicInitMarkStackPtr({:linear} tid:Tid, {:linear} mutatorTids:Set Piece)
modifies MarkStackPtr;
{ assert gcAndMutatorTids(tid, mutatorTids); MarkStackPtr := 0; }

yield procedure {:layer 95} InitMarkStackPtr({:layer 95} {:linear} tid:Tid, {:layer 95} {:linear} mutatorTids:Set Piece)
refines AtomicInitMarkStackPtr;
{
    call PrimitiveSetMarkStackPtr(0);
}

both action {:layer 96} AtomicSetMarkStackPtr({:linear} tid:Tid, val: int)
modifies MarkStackPtr;
{ assert tidHasLock(tid, absLock); MarkStackPtr := val; }

yield procedure {:layer 95} SetMarkStackPtr({:layer 95} {:linear} tid:Tid, val: int)
refines AtomicSetMarkStackPtr;
{
    call PrimitiveSetMarkStackPtr(val);
}

both action {:layer 96} AtomicReadMarkStack({:linear} tid:Tid, ptr: int) returns(val: int)
{ assert tidHasLock(tid, absLock); val := MarkStack[ptr]; }

yield procedure {:layer 95} ReadMarkStack({:layer 95} {:linear} tid:Tid, ptr: int) returns(val: int)
refines AtomicReadMarkStack;
{
    call val := PrimitiveReadMarkStack(ptr);
}

both action {:layer 96} AtomicWriteMarkStack({:linear} tid:Tid, ptr: int, val: int)
modifies MarkStack;
{ assert tidHasLock(tid, absLock); MarkStack[ptr] := val; }

yield procedure {:layer 95} WriteMarkStack({:layer 95} {:linear} tid:Tid, ptr: int, val: int)
refines AtomicWriteMarkStack;
{
    call PrimitiveWriteMarkStack(ptr, val);
}

both action {:layer 96,99} AtomicInitCollectorPhase({:linear} tid:Tid, {:linear} mutatorTids:Set Piece)
modifies collectorPhase;
{ assert gcAndMutatorTids(tid, mutatorTids); collectorPhase := IDLE(); }

yield procedure {:layer 95} InitCollectorPhase({:layer 95} {:linear} tid:Tid, {:layer 95} {:linear} mutatorTids:Set Piece)
refines AtomicInitCollectorPhase;
{
    call PrimitiveSetCollectorPhase(IDLE());
}

atomic action {:layer 96} AtomicReadCollectorPhase({:linear} tid: Tid) returns (phase:int)
{ assert tid == GcTid; phase := collectorPhase; }

yield procedure {:layer 95} ReadCollectorPhase({:layer 95} {:linear} tid: Tid) returns (phase:int)
refines AtomicReadCollectorPhase;
{
    call phase := PrimitiveReadCollectorPhase();
}

right action {:layer 96} AtomicReadCollectorPhaseLocked({:linear} tid: Tid) returns (phase:int)
{ assert mutatorTidWhole(tid) && tidHasLock(tid, absLock); phase := collectorPhase; }

yield procedure {:layer 95} ReadCollectorPhaseLocked({:layer 95} {:linear} tid: Tid) returns (phase:int)
refines AtomicReadCollectorPhaseLocked;
{
    call phase := PrimitiveReadCollectorPhase();
}

both action {:layer 96} AtomicSetCollectorPhase({:linear} tid: Tid, phase:int)
modifies collectorPhase;
{ assert tid == GcTid && tidHasLock(tid, absLock); collectorPhase := phase; }

yield procedure {:layer 95} SetCollectorPhase({:layer 95} {:linear} tid: Tid, phase:int)
refines AtomicSetCollectorPhase;
{
    call PrimitiveSetCollectorPhase(phase);
}

both action {:layer 96,99} AtomicInitMutatorPhase({:linear} tid:Tid, {:linear} mutatorTids:Set Piece, id: int)
modifies mutatorPhase;
{ assert gcAndMutatorTids(tid, mutatorTids); mutatorPhase[id] := IDLE(); }

yield procedure {:layer 95} InitMutatorPhase({:layer 95} {:linear} tid:Tid, {:layer 95} {:linear} mutatorTids:Set Piece, id: int)
refines AtomicInitMutatorPhase;
{
    call PrimitiveSetMutatorPhase(id, IDLE());
}

atomic action {:layer 96,100} AtomicReadMutatorPhaseByCollector({:linear} tid: Tid, i: int) returns (phase:int)
{ assert tid == GcTid; phase := mutatorPhase[i]; }

yield procedure {:layer 95} ReadMutatorPhaseByCollector({:layer 95} {:linear} tid: Tid, i: int) returns (phase:int)
refines AtomicReadMutatorPhaseByCollector;
{
    call phase := PrimitiveReadMutatorPhase(i);
}

both action {:layer 96,99} AtomicReadMutatorPhaseByMutator({:linear} tid: Tid, i: int) returns (phase:int)
{ assert mutatorTidWhole(tid) && tid->i == i; phase := mutatorPhase[i]; }

yield procedure {:layer 95} ReadMutatorPhaseByMutator({:layer 95} {:linear} tid: Tid, i: int) returns (phase:int)
refines AtomicReadMutatorPhaseByMutator;
{
    call phase := PrimitiveReadMutatorPhase(i);
}

atomic action {:layer 96} AtomicSetMutatorPhaseLocked({:linear} tid: Tid, i: int, phase: int)
modifies mutatorPhase;
{ assert mutatorTidWhole(tid) && tidHasLock(tid, absLock) && phase == collectorPhase && tid->i == i; mutatorPhase[i] := phase; }

yield procedure {:layer 95} SetMutatorPhaseLocked({:layer 95} {:linear} tid: Tid, i: int, phase: int)
refines AtomicSetMutatorPhaseLocked;
{
    call PrimitiveSetMutatorPhase(i, phase);
}

both action {:layer 96,99} AtomicInitSweepPtr({:linear} tid:Tid, {:linear} mutatorTids:Set Piece)
modifies sweepPtr;
{ assert gcAndMutatorTids(tid, mutatorTids); sweepPtr := memHi; }

yield procedure {:layer 95} InitSweepPtr({:layer 95} {:linear} tid:Tid, {:layer 95} {:linear} mutatorTids:Set Piece)
refines AtomicInitSweepPtr;
{
    call PrimitiveSetSweepPtr(memHi);
}

both action {:layer 96} AtomicReadSweepPtr({:linear} tid:Tid) returns(val:int)
{ assert tidHasLock(tid, absLock); val := sweepPtr; }

yield procedure {:layer 95} ReadSweepPtr({:layer 95} {:linear} tid:Tid) returns(val:int)
refines AtomicReadSweepPtr;
{
    call val := PrimitiveReadSweepPtr();
}

atomic action {:layer 96} AtomicSetSweepPtrLocked({:linear} tid:Tid, val: int)
modifies sweepPtr;
{ assert tid == GcTid && tidHasLock(tid, absLock); sweepPtr := val; }

yield procedure {:layer 95} SetSweepPtrLocked({:layer 95} {:linear} tid:Tid, val: int)
refines AtomicSetSweepPtrLocked;
{
    call PrimitiveSetSweepPtr(val);
}

atomic action {:layer 96} AtomicCollectorRootScanBarrierStartLocked({:linear} tid: Tid)
modifies rootScanOn;
{ assert tid == GcTid && tidHasLock(tid, absLock); rootScanOn := true; }

yield procedure {:layer 95} CollectorRootScanBarrierStartLocked({:layer 95} {:linear} tid: Tid)
refines AtomicCollectorRootScanBarrierStartLocked;
{
    call PrimitiveSetRootScanOn(true);
}

atomic action {:layer 96} AtomicCollectorRootScanBarrierEndLocked({:linear} tid: Tid)
modifies rootScanOn;
{ assert tid == GcTid && tidHasLock(tid, absLock); rootScanOn := false; }

yield procedure {:layer 95} CollectorRootScanBarrierEndLocked({:layer 95} {:linear} tid: Tid)
refines AtomicCollectorRootScanBarrierEndLocked;
{
    call PrimitiveSetRootScanOn(false);
}

right action {:layer 96} AtomicMutatorReadBarrierOn({:linear} tid: Tid) returns (val:bool)
{ assert tidHasLock(tid, absLock); val := rootScanOn; }

yield procedure {:layer 95} MutatorReadBarrierOn({:layer 95} {:linear} tid: Tid) returns (val:bool)
refines AtomicMutatorReadBarrierOn;
{
    call val := PrimitiveReadRootScanOn();
}

both action {:layer 96,99} AtomicPollMutatorReadBarrierOn({:linear} tid: Tid) returns (val:bool)
{ }

yield procedure {:layer 95} PollMutatorReadBarrierOn({:layer 95} {:linear} tid: Tid) returns (val:bool)
refines AtomicPollMutatorReadBarrierOn;
{
    call val := PrimitiveReadRootScanOn();
}

atomic action {:layer 96,99} AtomicInitRootScanBarrier({:linear} tid:Tid, {:linear} mutatorTids:Set Piece)
modifies rootScanBarrier;
{ assert gcAndMutatorTids(tid, mutatorTids); rootScanBarrier := numMutators; }

yield procedure {:layer 95} InitRootScanBarrier({:layer 95} {:linear} tid:Tid, {:layer 95} {:linear} mutatorTids:Set Piece)
refines AtomicInitRootScanBarrier;
{
    call PrimitiveSetRootScanBarrier(numMutators);
}

atomic action {:layer 96} AtomicCollectorRootScanBarrierRead({:linear} tid: Tid) returns (val:int)
{ assert tid == GcTid; val := rootScanBarrier; }

yield procedure {:layer 95} CollectorRootScanBarrierRead({:layer 95} {:linear} tid: Tid) returns (val:int)
refines AtomicCollectorRootScanBarrierRead;
{
    call val := PrimitiveReadRootScanBarrier();
}

atomic action {:layer 96} AtomicAddRootScanBarrier({:linear} tid_left: Tid, val: int)
modifies rootScanBarrier;
{ assert mutatorTidLeft(tid_left) && tidHasLock(tid_left, absLock); rootScanBarrier := rootScanBarrier + val; }

yield procedure {:layer 95} AddRootScanBarrier({:layer 95} {:linear} tid_left: Tid, val: int)
refines AtomicAddRootScanBarrier;
{
    call PrimitiveAddRootScanBarrier(val);
}

right action {:layer 96} AtomicMutatorsInRootScanBarrierAdd({:linear} tid_left: Tid, {:linear_in} tid_right: Tid)
modifies mutatorsInRootScanBarrier;
{
    var i: int;
    var {:linear} ps: Set Piece;
    var {:linear} p: One Piece;
    assert tidHasLock(tid_left, absLock) && mutatorTidRight(tid_right);
    Tid(i, ps) := tid_right;
    call p := One_Get(ps, Right(i));
    call One_Put(mutatorsInRootScanBarrier, p);
}

yield procedure {:layer 95} MutatorsInRootScanBarrierAdd({:layer 95} {:linear} tid_left: Tid, {:layer 95} {:linear_in} tid_right: Tid)
refines AtomicMutatorsInRootScanBarrierAdd;
{
    call {:layer 95} mutatorsInRootScanBarrier := PrimitiveMutatorsInRootScanBarrierAdd(tid_right, mutatorsInRootScanBarrier);
}

both action {:layer 96} AtomicMutatorsInRootScanBarrierRemove({:linear} tid_left: Tid) returns({:linear} tid_right: Tid)
modifies mutatorsInRootScanBarrier;
{
    var {:linear} ps: Set Piece;
    assert tidHasLock(tid_left, absLock) && !rootScanOn && mutatorTidLeft(tid_left) && Set_Contains(mutatorsInRootScanBarrier, Right(tid_left->i));
    call ps := Set_Get(mutatorsInRootScanBarrier, MapOne(Right(tid_left->i)));
    tid_right := Tid(tid_left->i, ps);
}

yield procedure {:layer 95} MutatorsInRootScanBarrierRemove({:layer 95} {:linear} tid_left: Tid) returns({:layer 95} {:linear} tid_right: Tid)
refines AtomicMutatorsInRootScanBarrierRemove;
ensures {:layer 95} tid_left->i == tid_right->i;
ensures {:layer 95} Set_Contains(tid_left->ps, Left(tid_left->i)) && Set_Contains(tid_right->ps, Right(tid_right->i));
{
    call {:layer 95} tid_right, mutatorsInRootScanBarrier := PrimitiveMutatorsInRootScanBarrierRemove(tid_left, mutatorsInRootScanBarrier);
}

both action {:layer 96,99} AtomicInitRoot({:linear} tid:Tid, {:linear} mutatorTids:Set Piece, x: int)
modifies root;
{ assert gcAndMutatorTids(tid, mutatorTids) && rootAddr(x); root[x] := 0; }

yield procedure {:layer 95} InitRoot({:layer 95} {:linear} tid:Tid, {:layer 95} {:linear} mutatorTids:Set Piece, x: int)
refines AtomicInitRoot;
{
    call PrimitiveWriteRoot(x, 0);
}

left action {:layer 96,99} AtomicReadRootInRootScanBarrier({:linear} tid:Tid, x: idx) returns (val: int)
{ assert tid == GcTid && rootAddr(x) && rootScanOn && mutatorsInRootScanBarrier == Mutators; val := root[x]; }

yield procedure {:layer 95} ReadRootInRootScanBarrier({:layer 95} {:linear} tid:Tid, x: idx) returns (val: int)
refines AtomicReadRootInRootScanBarrier;
{
    call val := PrimitiveReadRoot(x);
}

both action {:layer 96,99} AtomicWriteRoot({:linear} tid: Tid, i: idx, val: int)
modifies root;
{ assert mutatorTidWhole(tid) && rootAddr(i) && tidOwns(tid, i); root[i] := val; }

yield procedure {:layer 95} WriteRoot({:layer 95} {:linear} tid: Tid, i: idx, val: int)
refines AtomicWriteRoot;
{
    call PrimitiveWriteRoot(i, val);
}

both action {:layer 96,99} AtomicReadRoot({:linear} tid: Tid, i: idx) returns (val: int)
{ assert mutatorTidWhole(tid) && rootAddr(i) && tidOwns(tid, i); val := root[i]; }

yield procedure {:layer 95} ReadRoot({:layer 95} {:linear} tid: Tid, i: idx) returns (val: int)
refines AtomicReadRoot;
{
    call val := PrimitiveReadRoot(i);
}

both action {:layer 96,99} AtomicInitColor({:linear} tid:Tid, {:linear} mutatorTids:Set Piece, x: int)
modifies Color;
{ assert gcAndMutatorTids(tid, mutatorTids) && memAddr(x); Color[x] := UNALLOC(); }

yield procedure {:layer 95} InitColor({:layer 95} {:linear} tid:Tid, {:layer 95} {:linear} mutatorTids:Set Piece, x: int)
refines AtomicInitColor;
{
    call PrimitiveSetColor(x, UNALLOC());
}

both action {:layer 96} AtomicReadColorByCollector({:linear} tid:Tid, i: int) returns (val: int)
{ assert tid == GcTid && tidHasLock(tid, absLock) && memAddr(i); val := Color[i]; }

yield procedure {:layer 95} ReadColorByCollector({:layer 95} {:linear} tid:Tid, i: int) returns (val: int)
refines AtomicReadColorByCollector;
{
    call val := PrimitiveReadColor(i);
}

atomic action {:layer 96} AtomicReadColorByMutator1({:linear} tid:Tid, i: int) returns (val: int)
{ assert mutatorTidWhole(tid) && memAddr(i); }

yield procedure {:layer 95} ReadColorByMutator1({:layer 95} {:linear} tid:Tid, i: int) returns (val: int)
refines AtomicReadColorByMutator1;
{
    call val := PrimitiveReadColor(i);
}

both action {:layer 96} AtomicReadColorByMutator2({:linear} tid:Tid, i: int) returns (val: int)
{ assert mutatorTidWhole(tid) && tidHasLock(tid, absLock) && memAddr(i); val := Color[i]; }

yield procedure {:layer 95} ReadColorByMutator2({:layer 95} {:linear} tid:Tid, i: int) returns (val: int)
refines AtomicReadColorByMutator2;
{
    call val := PrimitiveReadColor(i);
}

atomic action {:layer 96,98} AtomicReadColorByMutator3({:linear} tid:Tid, i: int) returns (val: int)
{
    assert mutatorTidWhole(tid) && memAddr(i) && MarkPhase(mutatorPhase[tid->i]);
    assume White(Color[i]) ==> White(val);
}

yield procedure {:layer 95} ReadColorByMutator3({:layer 95} {:linear} tid:Tid, i: int) returns (val: int)
refines AtomicReadColorByMutator3;
{
    call val := PrimitiveReadColor(i);
}

both action {:layer 96} AtomicSetColor({:linear} tid:Tid, i: int, val: int)
modifies Color;
{ assert tidHasLock(tid, absLock) && memAddr(i) && PhaseConsistent(collectorPhase, mutatorPhase) && !MarkPhase(collectorPhase); Color[i] := val; }

yield procedure {:layer 95} SetColor({:layer 95} {:linear} tid:Tid, i: int, val: int)
refines AtomicSetColor;
{
    call PrimitiveSetColor(i, val);
}

left action {:layer 96} AtomicSetColorInMarkPhase({:linear} tid:Tid, i: int, val: int)
modifies Color;
{
    assert tidHasLock(tid, absLock) && memAddr(i);
    assert (MarkPhase(collectorPhase) || !PhaseConsistent(collectorPhase, mutatorPhase) ==> !White(val));
    Color[i] := val;
}

yield procedure {:layer 95} SetColorInMarkPhase({:layer 95} {:linear} tid:Tid, i: int, val: int)
refines AtomicSetColorInMarkPhase;
{
    call PrimitiveSetColor(i, val);
}

atomic action {:layer 96} AtomicSetColorInAlloc({:linear} tid:Tid, i: int, val: int, o: obj)
modifies Color, toAbs;
{
    assert tidHasLock(tid, absLock) && memAddr(i);
    assert White(val) ==> Unalloc(Color[i]);
    Color[i] := val;
    toAbs[i] := o;
}

yield procedure {:layer 95} SetColorInAlloc({:layer 95} {:layer 95} {:linear} tid:Tid, i: int, val: int, o: obj)
refines AtomicSetColorInAlloc;
{
    call PrimitiveSetColor(i, val);
    call {:layer 95} toAbs := Copy(toAbs[i := o]);
}

both action {:layer 96,99} AtomicInitToAbs({:linear} tid:Tid, {:linear} mutatorTids:Set Piece)
modifies toAbs;
{
    assert gcAndMutatorTids(tid, mutatorTids);
    toAbs := (lambda i:int :: if memAddr(i) then nil else Int(i));
}

yield procedure {:layer 95} InitToAbs({:layer 95} {:linear} tid:Tid, {:layer 95} {:linear} mutatorTids:Set Piece)
refines AtomicInitToAbs;
{
    call {:layer 95} toAbs := Copy((lambda i:int :: if memAddr(i) then nil else Int(i)));
}

right action {:layer 96} AtomicLockAcquire({:linear} tid: Tid)
modifies absLock;
{ assert tid->i != 0; assume absLock == 0; absLock := tid->i; }

yield procedure {:layer 95} LockAcquire({:layer 95} {:linear} tid: Tid)
refines AtomicLockAcquire;
preserves call Yield_Lock();
{
    var status:bool;
    while (true)
        invariant {:yields} true;
        invariant call Yield_Lock();
    {
        call status := PrimitiveLockCAS();
        if (status)
        {
            call {:layer 95} absLock := Copy(tid->i);
            return;
        }
    }
}

left action {:layer 96} AtomicLockRelease({:linear} tid:Tid)
modifies absLock;
{ assert tidHasLock(tid, absLock); absLock := 0; }

yield procedure {:layer 95} LockRelease({:layer 95} {:linear} tid:Tid)
refines AtomicLockRelease;
preserves call Yield_Lock();
{
    call PrimitiveLockClear();
    call {:layer 95} absLock := Copy(0);
}

yield invariant {:layer 95} Yield_Lock();
invariant lock <==> absLock != 0;

//////////////////////////////////////////////////////////////////////////////
// ATOMIC PRIMITIVES
//   The action specifications, linearity specifications, and requires/ensures below here are trusted.
//   (Note, though, that Boogie still verifies the mover types (atomic,left,right,both); these are not trusted.)
//////////////////////////////////////////////////////////////////////////////

pure action TidSplit({:linear_in} tid:Tid) returns({:linear} tid_left:Tid, {:linear} tid_right:Tid)
{
    var i: int;
    var {:linear} ps_right: Set Piece;
    i := tid->i;
    tid_left := tid;
    ps_right := Set_Singleton(Right(i));
    call Set_Split(tid_left->ps, ps_right);
    tid_right := Tid(i, ps_right);
}

pure action TidCombine({:linear_in} tid_left:Tid, {:linear_in} tid_right:Tid) returns({:linear} tid:Tid)
{
    var i: int;
    var {:linear} ps_right: Set Piece;
    var {:linear} p: One Piece;
    assert tid_left->i == tid_right->i;
    tid := tid_left;
    Tid(i, ps_right) := tid_right;
    call p := One_Get(ps_right, Right(i));
    call One_Put(tid->ps, p);
}

atomic action {:layer 1,95} AtomicPrimitiveReadField(x: int, f: fld) returns (y: int)
{ assert memAddr(x) && fieldAddr(f); y := mem[x][f]; }
yield procedure {:layer 0} PrimitiveReadField(x: int, f: fld) returns (y: int);
refines AtomicPrimitiveReadField;

atomic action {:layer 1,95} AtomicPrimitiveWriteField(x: int, f: fld, y: int)
modifies mem;
{ assert memAddr(x) && fieldAddr(f); mem[x][f] := y; }
yield procedure {:layer 0} PrimitiveWriteField(x: int, f: fld, y: int);
refines AtomicPrimitiveWriteField;

atomic action {:layer 1,95} AtomicPrimitiveReadMarkStackPtr() returns (val: int)
{ val := MarkStackPtr; }
yield procedure {:layer 0} PrimitiveReadMarkStackPtr() returns (val: int);
refines AtomicPrimitiveReadMarkStackPtr;

atomic action {:layer 1,95} AtomicPrimitiveSetMarkStackPtr(val: int)
modifies MarkStackPtr;
{ MarkStackPtr := val; }
yield procedure {:layer 0} PrimitiveSetMarkStackPtr(val: int);
refines AtomicPrimitiveSetMarkStackPtr;

atomic action {:layer 1,95} AtomicPrimitiveReadMarkStack(ptr: int) returns (val: int)
{ val := MarkStack[ptr]; }
yield procedure {:layer 0} PrimitiveReadMarkStack(ptr: int) returns (val: int);
refines AtomicPrimitiveReadMarkStack;

atomic action {:layer 1,95} AtomicPrimitiveWriteMarkStack(ptr: int, val: int)
modifies MarkStack;
{ MarkStack[ptr] := val; }
yield procedure {:layer 0} PrimitiveWriteMarkStack(ptr: int, val: int);
refines AtomicPrimitiveWriteMarkStack;

atomic action {:layer 1,95} AtomicPrimitiveReadCollectorPhase() returns (phase: int)
{ phase := collectorPhase; }
yield procedure {:layer 0} PrimitiveReadCollectorPhase() returns (phase: int);
refines AtomicPrimitiveReadCollectorPhase;

atomic action {:layer 1,95} AtomicPrimitiveSetCollectorPhase(phase:int)
modifies collectorPhase;
{ collectorPhase := phase; }
yield procedure {:layer 0} PrimitiveSetCollectorPhase(phase: int);
refines AtomicPrimitiveSetCollectorPhase;

atomic action {:layer 1,95} AtomicPrimitiveReadMutatorPhase(i: int) returns (phase: int)
{ phase := mutatorPhase[i]; }
yield procedure {:layer 0} PrimitiveReadMutatorPhase(i: int) returns (phase: int);
refines AtomicPrimitiveReadMutatorPhase;

atomic action {:layer 1,95} AtomicPrimitiveSetMutatorPhase(i: int, phase: int)
modifies mutatorPhase;
{ mutatorPhase[i] := phase; }
yield procedure {:layer 0} PrimitiveSetMutatorPhase(i: int, phase: int);
refines AtomicPrimitiveSetMutatorPhase;

atomic action {:layer 1,95} AtomicPrimitiveReadSweepPtr() returns(val: int)
{ val := sweepPtr; }
yield procedure {:layer 0} PrimitiveReadSweepPtr() returns(val: int);
refines AtomicPrimitiveReadSweepPtr;

atomic action {:layer 1,95} AtomicPrimitiveSetSweepPtr(val: int)
modifies sweepPtr;
{ sweepPtr := val; }
yield procedure {:layer 0} PrimitiveSetSweepPtr(val: int);
refines AtomicPrimitiveSetSweepPtr;

atomic action {:layer 1,95} AtomicPrimitiveReadRootScanOn() returns(val: bool)
{ val := rootScanOn; }
yield procedure {:layer 0} PrimitiveReadRootScanOn() returns(val: bool);
refines AtomicPrimitiveReadRootScanOn;

atomic action {:layer 1,95} AtomicPrimitiveSetRootScanOn(val: bool)
modifies rootScanOn;
{ rootScanOn := val; }
yield procedure {:layer 0} PrimitiveSetRootScanOn(val: bool);
refines AtomicPrimitiveSetRootScanOn;

atomic action {:layer 1,95} AtomicPrimitiveReadRootScanBarrier() returns(val: int)
{ val := rootScanBarrier; }
yield procedure {:layer 0} PrimitiveReadRootScanBarrier() returns(val: int);
refines AtomicPrimitiveReadRootScanBarrier;

atomic action {:layer 1,95} AtomicPrimitiveSetRootScanBarrier(val: int)
modifies rootScanBarrier;
{ rootScanBarrier := val; }
yield procedure {:layer 0} PrimitiveSetRootScanBarrier(val: int);
refines AtomicPrimitiveSetRootScanBarrier;

atomic action {:layer 1,95} AtomicPrimitiveAddRootScanBarrier(val: int)
modifies rootScanBarrier;
{ rootScanBarrier := rootScanBarrier + val; }
yield procedure {:layer 0} PrimitiveAddRootScanBarrier(val: int);
refines AtomicPrimitiveAddRootScanBarrier;

pure action PrimitiveMutatorsInRootScanBarrierAdd({:linear_in} tid_right: Tid, {:linear_in} mutatorsInRootScanBarrier: Set Piece)
    returns ({:linear} mutatorsInRootScanBarrier': Set Piece)
{
    var i: int;
    var {:linear} ps: Set Piece;
    var {:linear} p: One Piece;
    assert mutatorTidRight(tid_right);
    Tid(i, ps) := tid_right;
    call p := One_Get(ps, Right(i));
    mutatorsInRootScanBarrier' := mutatorsInRootScanBarrier;
    call One_Put(mutatorsInRootScanBarrier', p);
}

pure action PrimitiveMutatorsInRootScanBarrierRemove({:linear} tid_left: Tid, {:linear_in} mutatorsInRootScanBarrier: Set Piece)
    returns({:linear} tid_right: Tid, {:linear} mutatorsInRootScanBarrier': Set Piece)
{
    var {:linear} ps: Set Piece;
    assert mutatorTidLeft(tid_left);
    mutatorsInRootScanBarrier' := mutatorsInRootScanBarrier;
    call ps := Set_Get(mutatorsInRootScanBarrier', MapOne(Right(tid_left->i)));
    tid_right := Tid(tid_left->i, ps);
}

atomic action {:layer 1,95} AtomicPrimitiveWriteRoot(i: idx, val: int)
modifies root;
{ assert rootAddr(i); root[i] := val; }
yield procedure {:layer 0} PrimitiveWriteRoot(i: idx, val: int);
refines AtomicPrimitiveWriteRoot;

atomic action {:layer 1,95} AtomicPrimitiveReadRoot(i: idx) returns (val: int)
{ assert rootAddr(i); val := root[i]; }
yield procedure {:layer 0} PrimitiveReadRoot(i: idx) returns (val: int);
refines AtomicPrimitiveReadRoot;

atomic action {:layer 1,95} AtomicPrimitiveReadColor(i: int) returns (val: int)
{ assert memAddr(i); val := Color[i]; }
yield procedure {:layer 0} PrimitiveReadColor(i: int) returns (val: int);
refines AtomicPrimitiveReadColor;

atomic action {:layer 1,95} AtomicPrimitiveSetColor(i: int, val: int)
modifies Color;
{ assert memAddr(i); Color[i] := val; }
yield procedure {:layer 0} PrimitiveSetColor(i: int, val: int);
refines AtomicPrimitiveSetColor;

atomic action {:layer 1,95} AtomicPrimitiveLockCAS() returns (status: bool)
modifies lock;
{
    if (*) {
        assume !lock; lock := true; status := true;
    } else {
        status := false;
    }
}
yield procedure {:layer 0} PrimitiveLockCAS() returns (status: bool);
refines AtomicPrimitiveLockCAS;

atomic action {:layer 1,95} AtomicPrimitiveLockClear()
modifies lock;
{ lock := false; }
yield procedure {:layer 0} PrimitiveLockClear();
refines AtomicPrimitiveLockClear;
