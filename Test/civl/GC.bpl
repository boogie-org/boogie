//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

// RUN: %boogie -noinfer -useArrayTheory -typeEncoding:m "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type X = int;
function {:builtin "MapConst"} MapConstBool(bool): [X]bool;
function {:builtin "MapOr"} MapOr([X]bool, [X]bool) : [X]bool;
function {:builtin "MapNot"} MapNot(x: [X]bool) : [X]bool;
function {:inline} Subset(X: [X]bool, Y: [X]bool) : (bool)
{
    MapOr(MapNot(X), Y) == MapConstBool(true)
}

// Tid(i, left, right) represents a linear thread id for thread number i, where i > 0.
// Thread ids can be split into left and right fractions:
//   - For a whole thread id, both the left and right fields are true.
//   - For a fraction, either the left or right field is true.
// In other words, Tid(i, true, true) can be be split into Tid(i, true, false), Tid(i, false, true).
type{:datatype} Tid;
function{:constructor} Tid(i:int, left:bool, right:bool):Tid;

function {:inline} {:linear "tid"} TidCollector(x: Tid) : [X]bool
{
    MapConstBool(false)[-i#Tid(x) := left#Tid(x)][i#Tid(x) := right#Tid(x)]
}

function {:inline} {:linear "tid"} TidSetCollector(x: [X]bool) : [X]bool
{
    x
}

const numMutators: int;
axiom 0 < numMutators;
const GcTid: Tid;
axiom numMutators < i#Tid(GcTid) && left#Tid(GcTid) && right#Tid(GcTid);

function mutatorId(i: int) : bool { 1 <= i && i <= numMutators }
function mutatorTid(tid: Tid) : bool { mutatorId(i#Tid(tid)) }
function mutatorTidLeft(tid: Tid) : bool { mutatorTid(tid) && left#Tid(tid) }
function mutatorTidRight(tid: Tid) : bool { mutatorTid(tid) && right#Tid(tid) }
function mutatorTidWhole(tid: Tid) : bool { mutatorTid(tid) && left#Tid(tid) && right#Tid(tid) }
function gcAndMutatorTids(tid: Tid, mutatorTids: [int]bool) : bool
{
    tid == GcTid && (forall i:int :: mutatorId(i) ==> mutatorTids[i] && mutatorTids[-i])
}

function Size([int]bool) returns (int);
const Mutators: [int]bool;
axiom Size(Mutators) == numMutators;
axiom Size(MapConstBool(false)) == 0;
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
type{:datatype} obj;
function{:constructor} Nil():obj;
function{:constructor} Obj(id:int):obj;
function{:constructor} Int(i:int):obj;

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

function tidHasLock(tid:Tid, lock:int):bool { (tid == GcTid || mutatorTid(tid)) && lock == i#Tid(tid) && left#Tid(tid) }

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
function tidOwns(tid:Tid, x:idx):bool { owner(x) == i#Tid(tid) }

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

procedure {:yields} {:layer 100} Initialize({:linear_in "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool)
requires {:layer 97,98,99,100} tid == GcTid;
requires {:layer 97,98,99,100} (forall i:int :: mutatorId(i) ==> mutatorTids[i] && mutatorTids[-i]);
requires {:layer 99} mutatorsInRootScanBarrier == MapConstBool(false);
requires {:layer 100} (forall x: idx :: rootAddr(x) ==> rootAbs[x] == Int(0));
ensures {:layer 99} mutatorsInRootScanBarrier == MapConstBool(false);
ensures {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
ensures {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
{
    yield;
    assert {:layer 97,98,99,100} tid == GcTid;
    assert {:layer 97,98,99,100} (forall i:int :: mutatorId(i) ==> mutatorTids[i] && mutatorTids[-i]);
    assert {:layer 99} mutatorsInRootScanBarrier == MapConstBool(false);
    assert {:layer 100} (forall x: idx :: rootAddr(x) ==> rootAbs[x] == Int(0));

    call InitVars99(tid, mutatorTids);
    call InitVars100(tid, mutatorTids);

    async call GarbageCollect(tid);

    yield;
    assert {:layer 97,98,99,100} (forall i:int :: mutatorId(i) ==> mutatorTids[i] && mutatorTids[-i]);
    assert {:layer 99} mutatorsInRootScanBarrier == MapConstBool(false);
    assert {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
    assert {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
}

procedure {:atomic} {:layer 97,100} AtomicInitVars100({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool)
modifies mutatorPhase, root, toAbs, Color, mem, collectorPhase, sweepPtr;
{
    var memNew:[int][fld]int;
    var rootNew:[idx]int;
    var ColorNew:[int]int;
    var mutatorPhaseNew:[X]int;

    assert tid == GcTid;
    assert (forall i:int :: mutatorId(i) ==> mutatorTids[i] && mutatorTids[-i]);
    mem := memNew;
    root := rootNew;
    Color := ColorNew;
    mutatorPhase := mutatorPhaseNew;
    assume (forall x: int, f: fld :: memAddr(x) && fieldAddr(f) ==> mem[x][f] == x);
    assume (forall x: idx :: rootAddr(x) ==> root[x] == 0);
    assume (forall i:int :: memAddr(i) ==> Color[i] == UNALLOC());
    assume (forall i:int :: mutatorId(i) ==> mutatorPhase[i] == IDLE());
    toAbs := (lambda i:int :: if memAddr(i) then nil else Int(i));
    collectorPhase := IDLE();
    sweepPtr := memHi;
}
    
procedure {:yields} {:layer 96} {:refines "AtomicInitVars100"} InitVars100({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool)    
{
    var n:int;
    var m:int;
    yield;

    n := memLo;
    while (n < memHi)
        invariant{:layer 96} memLo <= n && n <= memHi;
        invariant{:layer 96} (forall i:int, f: fld :: memLo <= i && i < n && fieldAddr(f) ==> mem[i][f] == i);
    {
        m := 0;
        while (m < numFields)
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
        invariant{:layer 96} 0 <= n && n <= numRoots;
        invariant{:layer 96} (forall i:int :: 0 <= i && i < n ==> root[i] == 0);
    {
        call InitRoot(tid, mutatorTids, n);
        n := n + 1;
    }

    n := memLo;
    while (n < memHi)
        invariant{:layer 96} memLo <= n && n <= memHi;
        invariant{:layer 96} (forall i:int :: memLo <= i && i < n ==> Color[i] == UNALLOC());
    {
        call InitColor(tid, mutatorTids, n);
        n := n + 1;
    }

    n := 1;
    while (n <= numMutators)
        invariant{:layer 96} 1 <= n && n <= numMutators + 1;
        invariant{:layer 96} (forall i:int :: mutatorId(i) && i < n ==> mutatorPhase[i] == IDLE());
    {
        call InitMutatorPhase(tid, mutatorTids, n);
        n := n + 1;
    }

    call InitToAbs(tid, mutatorTids);
    call InitCollectorPhase(tid, mutatorTids);
    call InitSweepPtr(tid, mutatorTids);
    yield;
}

procedure {:yields} {:layer 99} InitVars99({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool)
requires {:layer 98,99} tid == GcTid;
requires {:layer 98,99} (forall i:int :: mutatorId(i) ==> mutatorTids[i] && mutatorTids[-i]);
ensures {:layer 99} mutatorsInRootScanBarrier == old(mutatorsInRootScanBarrier);
ensures {:layer 98} MarkStackPtr == 0;
ensures {:layer 99} rootScanBarrier == numMutators;
{
    yield;
    assert {:layer 98,99} tid == GcTid;
    assert {:layer 98,99} (forall i:int :: mutatorId(i) ==> mutatorTids[i] && mutatorTids[-i]);
    assert {:layer 99} mutatorsInRootScanBarrier == old(mutatorsInRootScanBarrier);
    call InitRootScanBarrier(tid, mutatorTids);
    call InitVars98(tid, mutatorTids);
    yield;
    assert {:layer 98,99} tid == GcTid;
    assert {:layer 98,99} (forall i:int :: mutatorId(i) ==> mutatorTids[i] && mutatorTids[-i]);
    assert {:layer 99} mutatorsInRootScanBarrier == old(mutatorsInRootScanBarrier);
    assert {:layer 98} MarkStackPtr == 0;
    assert {:layer 99} rootScanBarrier == numMutators;
}

procedure {:yields} {:layer 98} InitVars98({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool)
requires {:layer 98} tid == GcTid;
requires {:layer 98} (forall i:int :: mutatorId(i) ==> mutatorTids[i] && mutatorTids[-i]);
ensures {:layer 98} MarkStackPtr == 0;
{
    yield;
    assert {:layer 98} tid == GcTid;
    assert {:layer 98} (forall i:int :: mutatorId(i) ==> mutatorTids[i] && mutatorTids[-i]);
    call InitMarkStackPtr(tid, mutatorTids);
    yield;
    assert {:layer 98} tid == GcTid;
    assert {:layer 98} (forall i:int :: mutatorId(i) ==> mutatorTids[i] && mutatorTids[-i]);
    assert {:layer 98} MarkStackPtr == 0;
}

procedure {:atomic} {:layer 101} AtomicAlloc({:linear "tid"} tid:Tid, y:idx)
modifies allocSet, rootAbs, memAbs;
{
    var o: obj;
    assert mutatorTidWhole(tid) && rootAddr(y) && tidOwns(tid, y);
    assume (memAddrAbs(o) && !allocSet[o]);
    allocSet[o] := true;
    rootAbs[y] := o;
    memAbs[o] := (lambda z: int :: if (fieldAddr(z)) then o else memAbs[o][z]);
}

procedure {:yields} {:layer 100} {:refines "AtomicAlloc"} Alloc({:linear "tid"} tid:Tid, y:idx)
requires {:layer 95,96,99,100} mutatorTidWhole(tid);
requires {:layer 99} !mutatorsInRootScanBarrier[i#Tid(tid)] && RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
requires {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
ensures {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
{
    var ptr: int;
    var absPtr: obj;

    yield;
    assert {:layer 99} mutatorTidWhole(tid) && !mutatorsInRootScanBarrier[i#Tid(tid)] && RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
    assert {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);

    call TestRootScanBarrier(tid);

    yield;
    assert {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);

    call UpdateMutatorPhase(tid);

    yield;
    assert {:layer 100} mutatorTidWhole(tid) && tidOwns(tid, y);
    assert {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);

    call ptr, absPtr := AllocRaw(tid, y);

    yield;
    assert {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
}

procedure {:yields} {:layer 99} TestRootScanBarrier({:linear "tid"} tid:Tid)
requires {:layer 95,96,99} mutatorTidWhole(tid);
requires {:layer 99} !mutatorsInRootScanBarrier[i#Tid(tid)] && RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
{
    var isRootScanOn: bool;
    var{:linear "tid"} tid_tmp: Tid;

    yield;
    assert {:layer 99} mutatorTidWhole(tid) && !mutatorsInRootScanBarrier[i#Tid(tid)] && RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
    call isRootScanOn := PollMutatorReadBarrierOn(tid);
    yield;
    assert {:layer 99} mutatorTidWhole(tid) && !mutatorsInRootScanBarrier[i#Tid(tid)] && RootScanBarrierInv( mutatorsInRootScanBarrier, rootScanBarrier);
    if (isRootScanOn)
    {
        assert{:layer 99} mutatorsInRootScanBarrier == mutatorsInRootScanBarrier[i#Tid(tid) := false];
        call tid_tmp := MutatorRootScanBarrierEnter(tid);

        yield;
        assert {:layer 99} mutatorTidLeft(tid_tmp) && mutatorsInRootScanBarrier[i#Tid(tid_tmp)] && RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);

        assert{:layer 99} mutatorsInRootScanBarrier == mutatorsInRootScanBarrier[i#Tid(tid_tmp) := true];
        call tid_tmp := MutatorRootScanBarrierWait(tid_tmp);
        call TidOutput(tid_tmp, tid);
    }
    yield;
}

procedure {:atomic} {:layer 101} AtomicWriteField({:linear "tid"} tid:Tid, x: idx, f: fld, y: idx) // x.f = y
modifies memAbs;
{ assert mutatorTidWhole(tid) && rootAddr(x) && tidOwns(tid, x) && fieldAddr(f) && rootAddr(y) && tidOwns(tid, y) && memAddrAbs(rootAbs[x]); memAbs[rootAbs[x]][f] := rootAbs[y]; }

procedure {:yields} {:layer 100} {:refines "AtomicWriteField"} WriteField({:linear "tid"} tid:Tid, x: idx, f: fld, y: idx)
requires {:layer 98,100} mutatorTidWhole(tid);
requires {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
ensures {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
{
    yield;
    assert {:layer 98,100} mutatorTidWhole(tid);
    assert {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);

    call WriteBarrier(tid, y);

    yield;
    assert {:layer 98,100} mutatorTidWhole(tid);
    assert {:layer 100} mutatorTidWhole(tid) && tidOwns(tid, x) && tidOwns(tid, y);
    assert {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
    assert {:layer 100} memAddr(root[y]) && MarkPhase(mutatorPhase[i#Tid(tid)]) ==> Gray(Color[root[y]]) || Black(Color[root[y]]);

    call WriteFieldRaw(tid, x, f, y);

    yield;
    assert {:layer 98,100} mutatorTidWhole(tid);
    assert {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
}

procedure {:atomic} {:layer 101} AtomicReadField({:linear "tid"} tid:Tid, x: idx, f: fld, y: idx) // y = x.f
modifies rootAbs;
{ assert mutatorTidWhole(tid) && rootAddr(x) && tidOwns(tid, x) && fieldAddr(f) && rootAddr(y) && tidOwns(tid, y) && memAddrAbs(rootAbs[x]); rootAbs[y] := memAbs[rootAbs[x]][f]; }

procedure {:yields} {:layer 100} {:refines "AtomicReadField"} ReadField({:linear "tid"} tid:Tid, x: idx, f: fld, y: idx)
requires {:layer 99} mutatorTidWhole(tid);
requires {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
ensures  {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
{
    yield;
    assert {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
    assert {:layer 99} mutatorTidWhole(tid) && !mutatorsInRootScanBarrier[i#Tid(tid)];
    call ReadFieldRaw(tid, x, f, y);
    yield;
    assert {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
}

procedure {:atomic} {:layer 101} AtomicEq({:linear "tid"} tid:Tid, x: idx, y:idx) returns (isEqual:bool)
{ assert mutatorTidWhole(tid) && rootAddr(x) && tidOwns(tid, x) && rootAddr(y) && tidOwns(tid, y); isEqual := rootAbs[x] == rootAbs[y]; }

procedure {:yields} {:layer 100} {:refines "AtomicEq"} Eq({:linear "tid"} tid:Tid, x: idx, y:idx) returns (isEqual:bool)
requires {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
ensures {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
{
    yield;
    assert {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
    call isEqual := EqRaw(tid, x, y);
    yield;
    assert {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
}

procedure {:yields} {:layer 97} YieldWaitForMutators({:linear "tid"} tid:Tid, nextPhase: int, done: bool, i: int)
requires {:layer 97} tid == GcTid;
requires {:layer 97} nextPhase == collectorPhase;
requires {:layer 97} done ==> (forall j:int:: 1 <= j && j < i ==> nextPhase == mutatorPhase[j]);
ensures {:layer 97} nextPhase == collectorPhase;
ensures {:layer 97} done ==> (forall j:int:: 1 <= j && j < i ==> nextPhase == mutatorPhase[j]);
{
  yield;
  assert {:layer 97} tid == GcTid;
  assert {:layer 97} nextPhase == collectorPhase;
  assert {:layer 97} done ==> (forall j:int:: 1 <= j && j < i ==> nextPhase == mutatorPhase[j]);
}

procedure {:atomic} {:layer 98,100} AtomicWaitForMutators({:linear "tid"} tid:Tid, nextPhase: int)
{
     assert tid == GcTid;
     assume (forall j:int:: mutatorId(j) ==> nextPhase == mutatorPhase[j]);
}

procedure {:yields} {:layer 97} {:refines "AtomicWaitForMutators"} WaitForMutators({:linear "tid"} tid:Tid, nextPhase: int)
requires {:layer 97} tid == GcTid;
requires {:layer 97} nextPhase == collectorPhase;
{
    var done: bool;
    var i: int;
    var mutatorPhaseLocal: int;

    done := false;
    call YieldWaitForMutators(tid, nextPhase, done, 1);
    while (!done)
    invariant {:layer 97} nextPhase == collectorPhase;
    invariant {:layer 97} done ==> (forall j:int:: mutatorId(j) ==> nextPhase == mutatorPhase[j]);
    {
        done := true;
        i := 1;
        call YieldWaitForMutators(tid, nextPhase, done, i);
        while (i <= numMutators)
          invariant {:layer 97} nextPhase == collectorPhase;
          invariant {:layer 97} done ==> (forall j:int:: 1 <= j && j < i ==> nextPhase == mutatorPhase[j]);
        {
            call mutatorPhaseLocal := ReadMutatorPhaseByCollector(tid, i);
            if (nextPhase != mutatorPhaseLocal)
            {
                done := false;
            }
            i := i + 1;
            call YieldWaitForMutators(tid, nextPhase, done, i);
        }
    }
    call YieldWaitForMutators(tid, nextPhase, done, numMutators+1);
}

procedure {:yields} {:layer 100} YieldGarbageCollect({:linear "tid"} tid:Tid)
requires {:layer 97,98,99,100} tid == GcTid;
requires {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
requires {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
requires {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
requires {:layer 100} (forall x: int :: memAddr(x) ==> (toAbs[x] == nil <==> Unalloc(Color[x])));
requires {:layer 100} sweepPtr == memHi ==> (forall x: int :: memAddr(x) ==> !Black(Color[x]));
requires {:layer 100}
         sweepPtr == memLo ==>
              (forall x: int :: memAddr(x) ==> !Gray(Color[x])) &&
       (forall i: int :: rootAddr(i) && memAddr(root[i]) ==> Black(Color[root[i]])) &&
           (forall x: int, f: fld :: memAddr(x) && Black(Color[x]) && fieldAddr(f) && memAddr(mem[x][f]) ==> Black(Color[mem[x][f]]));
ensures {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
ensures {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
ensures {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
ensures {:layer 100} (forall x: int :: memAddr(x) ==> (toAbs[x] == nil <==> Unalloc(Color[x])));
ensures {:layer 100} sweepPtr == memHi ==> (forall x: int :: memAddr(x) ==> !Black(Color[x]));
ensures {:layer 100}
         sweepPtr == memLo ==>
              (forall x: int :: memAddr(x) ==> !Gray(Color[x])) &&
       (forall i: int :: rootAddr(i) && memAddr(root[i]) ==> Black(Color[root[i]])) &&
           (forall x: int, f: fld :: memAddr(x) && Black(Color[x]) && fieldAddr(f) && memAddr(mem[x][f]) ==> Black(Color[mem[x][f]]));
ensures {:layer 97,99,100} old(collectorPhase) == collectorPhase;
ensures {:layer 99,100} old(sweepPtr) == sweepPtr;
ensures {:layer 98} collectorPhase == old(collectorPhase);
{
    yield;
    assert {:layer 97,98,99,100} tid == GcTid;
    assert {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
    assert {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
    assert {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
    assert {:layer 100} (forall x: int :: memAddr(x) ==> (toAbs[x] == nil <==> Unalloc(Color[x])));
    assert {:layer 100} sweepPtr == memHi ==> (forall x: int :: memAddr(x) ==> !Black(Color[x]));
    assert {:layer 100}
         sweepPtr == memLo ==>
              (forall x: int :: memAddr(x) ==> !Gray(Color[x])) &&
       (forall i: int :: rootAddr(i) && memAddr(root[i]) ==> Black(Color[root[i]])) &&
           (forall x: int, f: fld :: memAddr(x) && Black(Color[x]) && fieldAddr(f) && memAddr(mem[x][f]) ==> Black(Color[mem[x][f]]));
    assert {:layer 97,99,100} old(collectorPhase) == collectorPhase;
    assert {:layer 99,100} old(sweepPtr) == sweepPtr;
    assert {:layer 98} collectorPhase == old(collectorPhase);
}

procedure {:yields} {:layer 100} GarbageCollect({:linear "tid"} tid:Tid)
requires {:layer 97,98,99,100} tid == GcTid;
requires {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
requires {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
requires {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
requires {:layer 100} (forall x: int :: memAddr(x) ==> (toAbs[x] == nil <==> Unalloc(Color[x])));
requires {:layer 98,100} IdlePhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase);
requires {:layer 100} (forall x: int :: memAddr(x) ==> !Black(Color[x]));
requires {:layer 100} sweepPtr == memHi;
{
    var nextPhase: int;

    call YieldGarbageCollect(tid);
    while (*)
    invariant {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
    invariant {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
    invariant {:layer 98,100} IdlePhase(collectorPhase);
    invariant {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
    invariant {:layer 100} (forall x: int :: memAddr(x) ==> (toAbs[x] == nil <==> Unalloc(Color[x])));
    invariant {:layer 100} (forall x: int :: memAddr(x) ==> !Black(Color[x]));
    invariant {:layer 100} sweepPtr == memHi;
    {
        call nextPhase := HandshakeCollector(tid); // IDLE --> MARK
        call YieldGarbageCollect(tid);
        call WaitForMutators(tid, nextPhase);
        assert {:layer 98} MarkPhase(collectorPhase);
        call MarkOuterLoop(tid);
        assert {:layer 98} MarkPhase(collectorPhase);
        call nextPhase := HandshakeCollector(tid); // MARK --> SWEEP
        assert {:layer 98} SweepPhase(collectorPhase);
        call YieldGarbageCollect(tid);
        call WaitForMutators(tid, nextPhase);
        assert {:layer 98} SweepPhase(collectorPhase);
        assert {:layer 98} PhaseConsistent(collectorPhase, mutatorPhase);
        call Sweep(tid);
        call nextPhase := HandshakeCollector(tid); // SWEEP --> IDLE
        call YieldGarbageCollect(tid);
    }
    yield;
}

procedure {:yields} {:layer 100} YieldMarkBegin({:linear "tid"} tid:Tid)
requires {:layer 98,99,100} tid == GcTid;
requires {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
requires {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
requires {:layer 100} MarkPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase) && sweepPtr == memHi;
requires {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
requires {:layer 100} (forall x: int :: memAddr(x) ==> (toAbs[x] == nil <==> Unalloc(Color[x])));
requires {:layer 100} (forall x: int :: memAddr(x) ==> !Black(Color[x]));
ensures {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
ensures {:layer 98} collectorPhase == old(collectorPhase);
ensures {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
ensures {:layer 100} MarkPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase);
ensures {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
ensures {:layer 100} (forall x: int :: memAddr(x) ==> (toAbs[x] == nil <==> Unalloc(Color[x])));
ensures {:layer 100} (forall x: int :: memAddr(x) ==> !Black(Color[x]));
{
    yield;
    assert {:layer 98,99,100} tid == GcTid;
    assert {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
    assert {:layer 98} collectorPhase == old(collectorPhase);
    assert {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
    assert {:layer 100} MarkPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase) && sweepPtr == memHi;
    assert {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
    assert {:layer 100} (forall x: int :: memAddr(x) ==> (toAbs[x] == nil <==> Unalloc(Color[x])));
    assert {:layer 100} (forall x: int :: memAddr(x) ==> !Black(Color[x]));
}

procedure {:yields} {:layer 100} YieldMark({:linear "tid"} tid:Tid)
requires {:layer 98,99,100} tid == GcTid;
requires {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
requires {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
requires {:layer 100} MarkPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase) && sweepPtr == memLo;
requires {:layer 100} MarkInv(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
ensures {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
ensures {:layer 98} collectorPhase == old(collectorPhase);
ensures {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
ensures {:layer 100} MarkPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase) && sweepPtr == memLo;
ensures {:layer 100} MarkInv(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
ensures {:layer 100} (forall x: int :: memAddr(x) && !Unalloc(old(Color)[x]) ==> !Unalloc(Color[x]));
ensures {:layer 100} (forall x: int :: memAddr(x) && !Unalloc(old(Color)[x]) && !White(old(Color)[x]) ==> !White(Color[x]));
{
    yield;
    assert {:layer 98,99,100} tid == GcTid;
    assert {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
    assert {:layer 98} collectorPhase == old(collectorPhase);
    assert {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
    assert {:layer 100} MarkPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase) && sweepPtr == memLo;
    assert {:layer 100} MarkInv(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
    assert {:layer 100} (forall x: int :: memAddr(x) && !Unalloc(old(Color)[x]) ==> !Unalloc(Color[x]));
    assert {:layer 100} (forall x: int :: memAddr(x) && !Unalloc(old(Color)[x]) && !White(old(Color)[x]) ==> !White(Color[x]));
}

procedure {:yields} {:layer 100} YieldMarkEnd({:linear "tid"} tid:Tid)
requires {:layer 98,99,100} tid == GcTid;
requires {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
requires {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
requires {:layer 100} MarkPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase) && sweepPtr == memLo;
requires {:layer 100} MarkInv(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
requires {:layer 100} (forall x: int :: memAddr(x) ==> !Gray(Color[x]));
requires {:layer 100} (forall i: int :: rootAddr(i) && memAddr(root[i]) ==> Black(Color[root[i]]));
ensures {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
ensures {:layer 98} collectorPhase == old(collectorPhase);
ensures {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
ensures {:layer 100} MarkPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase) && sweepPtr == memLo;
ensures {:layer 100} MarkInv(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
ensures {:layer 100} (forall x: int :: memAddr(x) ==> !Gray(Color[x]));
ensures {:layer 100} (forall i: int :: rootAddr(i) && memAddr(root[i]) ==> Black(Color[root[i]]));
{
    yield;
    assert {:layer 98,99,100} tid == GcTid;
    assert {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
    assert {:layer 98} collectorPhase == old(collectorPhase);
    assert {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
    assert {:layer 100} MarkPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase) && sweepPtr == memLo;
    assert {:layer 100} MarkInv(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
    assert {:layer 100} (forall x: int :: memAddr(x) ==> !Gray(Color[x]));
    assert {:layer 100} (forall i: int :: rootAddr(i) && memAddr(root[i]) ==> Black(Color[root[i]]));
}

procedure {:yields} {:layer 100} MarkOuterLoop({:linear "tid"} tid:Tid)
requires {:layer 98,99,100} tid == GcTid;
requires {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
requires {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
requires {:layer 100} Iso(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
requires {:layer 100} (forall x: int :: memAddr(x) ==> (toAbs[x] == nil <==> Unalloc(Color[x])));
requires {:layer 100} (forall x: int :: memAddr(x) ==> !Black(Color[x]));
requires {:layer 100} MarkPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase) && sweepPtr == memHi;
ensures {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
ensures {:layer 98} collectorPhase == old(collectorPhase);
ensures {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
ensures {:layer 100} MarkPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase) && sweepPtr == memLo;
ensures {:layer 100} MarkInv(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
ensures {:layer 100} (forall x: int :: memAddr(x) ==> !Gray(Color[x]));
ensures {:layer 100} (forall i: int :: rootAddr(i) && memAddr(root[i]) ==> Black(Color[root[i]]));
{
    var canStop: bool;

    call YieldMarkBegin(tid);
    call ResetSweepPtr(tid);
    call YieldMark(tid);
    while (true)
    invariant {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
    invariant {:layer 98} collectorPhase == old(collectorPhase);
    invariant {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
    invariant {:layer 100} MarkInv(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
    invariant {:layer 100} MarkPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase) && sweepPtr == memLo;
    {
        call canStop := CanMarkStop(tid);
        if (canStop)
        {
            call YieldMarkEnd(tid);
            return;
        }
        call MarkInnerLoop(tid);
    }
    call YieldMarkEnd(tid);
}

procedure {:yields} {:layer 100} MarkInnerLoop({:linear "tid"} tid:Tid)
requires {:layer 98,99,100} tid == GcTid;
requires {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
requires {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
requires {:layer 100} MarkPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase) && sweepPtr == memLo;
requires {:layer 100} MarkInv(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
ensures {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
ensures {:layer 98} collectorPhase == old(collectorPhase);
ensures {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
ensures {:layer 100} MarkPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase) && sweepPtr == memLo;
ensures {:layer 100} MarkInv(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
{
  var nodeProcessed:int;
  var fldIter: int;
  var isEmpty: bool;
  var child: int;

  call YieldMark(tid);
  while (true)
  invariant {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
  invariant {:layer 100} MarkInv(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
  invariant {:layer 100} MarkPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase) && sweepPtr == memLo;
  invariant {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
  invariant {:layer 98} collectorPhase == old(collectorPhase);
  {
    call isEmpty, nodeProcessed := SET_Peek(tid);
    if (isEmpty) {
      break;
    }
    fldIter := 0;
    while (fldIter < numFields)
    invariant {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, nodeProcessed);
    invariant {:layer 98} collectorPhase == old(collectorPhase);
    invariant {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
    invariant {:layer 100} MarkPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase) && sweepPtr == memLo;
    invariant {:layer 100} !Unalloc(Color[nodeProcessed]);
    invariant {:layer 100} MarkInv(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
    invariant {:layer 100} 0 <= fldIter && fldIter <= numFields;
    invariant {:layer 100} (forall x: int :: 0 <= x && x < fldIter && memAddr(mem[nodeProcessed][x]) ==> !Unalloc(Color[mem[nodeProcessed][x]]) && !White(Color[mem[nodeProcessed][x]]));
    {
      call child := ReadFieldCollector(tid, nodeProcessed, fldIter);
      if (memAddr(child))
      {
        call SET_InsertIntoSetIfWhite(tid, nodeProcessed, child);
      }
      fldIter := fldIter + 1;
      yield;
      assert {:layer 98,99,100} tid == GcTid;
      assert {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, nodeProcessed);
      assert {:layer 98} collectorPhase == old(collectorPhase);
      assert {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
      assert {:layer 100} MarkPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase) && sweepPtr == memLo;
      assert {:layer 100} !Unalloc(Color[nodeProcessed]);
      assert {:layer 100} MarkInv(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
      assert {:layer 100} (forall x: int :: 0 <= x && x < fldIter && memAddr(mem[nodeProcessed][x]) ==> !Unalloc(Color[mem[nodeProcessed][x]]) && !White(Color[mem[nodeProcessed][x]]));
    }
    call SET_RemoveFromSet(tid, nodeProcessed);
    call YieldMark(tid);
  }
  call YieldMark(tid);
}

procedure {:atomic} {:layer 100} AtomicCanMarkStop({:linear "tid"} tid:Tid) returns (canStop: bool)
modifies Color;
{
    var oldColor, newColor: [int]int;
    assert tid == GcTid;
    oldColor := Color;
    Color := newColor;
    assume (forall u: int :: if memAddr(u) && White(oldColor[u]) && (exists k: int :: rootAddr(k) && root[k] == u) then Color[u] == GRAY() else Color[u] == oldColor[u]);
    canStop := (forall v: int :: memAddr(v) ==> !Gray(Color[v]));
}

procedure {:yields} {:layer 99} {:refines "AtomicCanMarkStop"} CanMarkStop({:linear "tid"} tid:Tid) returns (canStop: bool)
requires {:layer 98,99} tid == GcTid;
requires {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
ensures {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
ensures {:layer 98} collectorPhase == old(collectorPhase);
requires {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
ensures {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
{
    var i: int;
    var o: int;
    var {:layer 99} snapColor: [int]int;

    yield;
    assert {:layer 98,99} tid == GcTid;
    assert {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
    assert {:layer 98} collectorPhase == old(collectorPhase);
    assert {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
    call CollectorRootScanBarrierStart(tid);
    yield;
    assert {:layer 98,99} tid == GcTid;
    assert {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
    assert {:layer 98} collectorPhase == old(collectorPhase);
    assert {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier) && rootScanOn;
    call snapColor := GhostReadColor99();
    call CollectorRootScanBarrierWait(tid);

    i := 0;
    while (i < numRoots)
    invariant {:terminates} {:layer 96,97,98,99} true;
    invariant {:layer 99} Mutators == mutatorsInRootScanBarrier && rootScanOn;
    invariant {:layer 99} 0 <= i && i <= numRoots;
    invariant {:layer 99} Color == (lambda u: int :: if memAddr(u) && White(snapColor[u]) && (exists k: int :: 0 <= k && k < i && root[k] == u) then GRAY() else snapColor[u]);
    invariant {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
    invariant {:layer 98} collectorPhase == old(collectorPhase);
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
    yield;
    assert {:layer 98,99} tid == GcTid;
    assert {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
    assert {:layer 98} collectorPhase == old(collectorPhase);
    assert {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
}

procedure {:yields} {:layer 100} YieldSweepBegin({:linear "tid"} tid:Tid, localSweepPtr: int, fldIter: int, isInit: bool)
requires {:layer 98,99,100} tid == GcTid;
requires {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
requires {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
requires {:layer 98,100} SweepPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase);
requires {:layer 100} sweepPtr == memLo;
requires {:layer 100} !isInit ==> SweepInv(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
requires {:layer 100} isInit ==> SweepInvInit(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
requires {:layer 100} (forall i: int :: rootAddr(i) && memAddr(root[i]) ==> Black(Color[root[i]]));
requires {:layer 100} (forall x: int, f: fld :: memLo <= x && x < localSweepPtr && (Unalloc(Color[x]) || White(Color[x])) && fieldAddr(f) ==> mem[x][f] == x);
requires {:layer 100} (forall f: fld :: 0 <= f && f < fldIter ==> mem[localSweepPtr][f] == localSweepPtr);
requires {:layer 100} fldIter == 0 || White(Color[localSweepPtr]);
ensures {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
ensures {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
ensures {:layer 98,100} SweepPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase);
ensures {:layer 100} !isInit ==> SweepInv(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
ensures {:layer 100} isInit ==> SweepInvInit(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
ensures {:layer 100} (forall i: int :: rootAddr(i) && memAddr(root[i]) ==> Black(Color[root[i]]));
ensures {:layer 100} sweepPtr == memLo;
ensures {:layer 100} (forall x: int :: memAddr(x) && !Unalloc(old(Color)[x]) ==> old(Color)[x] == Color[x]);
ensures {:layer 100} (forall x: int, f: fld :: memLo <= x && x < localSweepPtr && (Unalloc(Color[x]) || White(Color[x])) && fieldAddr(f) ==> mem[x][f] == x);
ensures {:layer 100} (forall f: fld :: 0 <= f && f < fldIter ==> mem[localSweepPtr][f] == localSweepPtr);
ensures {:layer 100} fldIter == 0 || White(Color[localSweepPtr]);
{
    yield;
    assert {:layer 98,99,100} tid == GcTid;
    assert {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
    assert {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
    assert {:layer 98,100} SweepPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase);
    assert {:layer 100} sweepPtr == memLo;
    assert {:layer 100} !isInit ==> SweepInv(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
    assert {:layer 100} isInit ==> SweepInvInit(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
    assert {:layer 100} (forall i: int :: rootAddr(i) && memAddr(root[i]) ==> Black(Color[root[i]]));
    assert {:layer 100} (forall x: int :: memAddr(x) && !Unalloc(old(Color)[x]) ==> old(Color)[x] == Color[x]);
    assert {:layer 100} (forall x: int, f: fld :: memLo <= x && x < localSweepPtr && (Unalloc(Color[x]) || White(Color[x])) && fieldAddr(f) ==> mem[x][f] == x);
    assert {:layer 100} (forall f: fld :: 0 <= f && f < fldIter ==> mem[localSweepPtr][f] == localSweepPtr);
    assert {:layer 100} fldIter == 0 || White(Color[localSweepPtr]);
}

procedure {:yields} {:layer 100} YieldSweepEnd({:linear "tid"} tid:Tid)
requires {:layer 98,99,100} tid == GcTid;
requires {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
requires {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
requires {:layer 98,100} SweepPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase);
requires {:layer 100} sweepPtr == memHi;
requires {:layer 100} SweepInv(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
requires {:layer 100} (forall x: int :: memAddr(x) ==> !Black(Color[x]));
ensures {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
ensures {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
ensures {:layer 98,100} SweepPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase);
ensures {:layer 100} SweepInv(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
ensures {:layer 100} (forall x: int :: memAddr(x) ==> !Black(Color[x]));
ensures {:layer 100} sweepPtr == memHi;
{
    yield;
    assert {:layer 98,99,100} tid == GcTid;
    assert {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
    assert {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
    assert {:layer 98,100} SweepPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase);
    assert {:layer 100} SweepInv(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
    assert {:layer 100} (forall x: int :: memAddr(x) ==> !Black(Color[x]));
    assert {:layer 100} sweepPtr == memHi;
}

procedure {:yields} {:layer 100} Sweep({:linear "tid"} tid:Tid)
requires {:layer 98,99,100} tid == GcTid;
requires {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
requires {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
requires {:layer 98,100} SweepPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase);
requires {:layer 100} sweepPtr == memLo;
requires {:layer 100} (forall i: int :: rootAddr(i) && memAddr(root[i]) ==> Black(Color[root[i]]));
requires {:layer 100} SweepInv(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
ensures {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
ensures {:layer 99} RootScanBarrierInv(mutatorsInRootScanBarrier, rootScanBarrier);
ensures {:layer 100} SweepInv(root, rootAbs, mem, memAbs, Color, toAbs, allocSet);
ensures {:layer 100} (forall x: int :: memAddr(x) ==> !Black(Color[x]));
ensures {:layer 100} sweepPtr == memHi;
ensures {:layer 98,100} SweepPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase);
{
  var localSweepPtr: int;
  var {:layer 100} snapColor: [int]int;

  localSweepPtr := memLo;
  call YieldSweepBegin(tid, localSweepPtr, 0, false);
  call ClearToAbsWhite(tid);
  call YieldSweepBegin(tid, localSweepPtr, 0, true);

  call snapColor := GhostReadColor100();
  while (localSweepPtr < memHi)
  invariant {:terminates} {:layer 97,98,99,100} true;
  invariant {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
  invariant {:layer 98,100} SweepPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase);
  invariant {:layer 100} localSweepPtr == sweepPtr && memLo <= sweepPtr && sweepPtr <= memHi;
  invariant {:layer 100} (forall i: int :: rootAddr(i) && memAddr(root[i]) ==> Black(snapColor[root[i]]));
  invariant {:layer 100} SweepInvInit(root, rootAbs, mem, memAbs, snapColor, toAbs, allocSet);
  invariant {:layer 100} (forall i:int:: memAddr(i) ==> if sweepPtr <= i then Color[i] == snapColor[i] else if Black(snapColor[i]) then White(Color[i]) else Unalloc(Color[i]));
  {
    call SweepNext(tid);
    localSweepPtr := localSweepPtr + 1;
  }
  call YieldSweepEnd(tid);
}

procedure {:atomic} {:layer 100} AtomicWriteFieldRaw({:linear "tid"} tid:Tid, x: idx, f: fld, y: idx)
modifies memAbs,  mem;
{
    assert mutatorTidWhole(tid) && rootAddr(x) && tidOwns(tid, x) && fieldAddr(f) && rootAddr(y) && tidOwns(tid, y) && memAddr(root[x]) && toAbs[root[x]] != nil && memAddrAbs(rootAbs[x]);
    memAbs[rootAbs[x]][f] := rootAbs[y];
    mem[root[x]][f] := root[y];
}

procedure {:yields} {:layer 99} {:refines "AtomicWriteFieldRaw"} WriteFieldRaw({:linear "tid"} tid:Tid, x: idx, f: fld, y: idx)
requires {:layer 98} mutatorTidWhole(tid);
{
    var valx: int;
    var valy: int;

    yield;
    assert {:layer 98} mutatorTidWhole(tid);
    call valx := ReadRoot(tid, x);
    call valy := ReadRoot(tid, y);
    call WriteFieldGeneral(tid, valx, f, valy);
    call SetMemAbs1(x, f, y);
    yield;
    assert {:layer 98} mutatorTidWhole(tid);
}

procedure {:atomic} {:layer 100} AtomicReadFieldRaw({:linear "tid"} tid:Tid, x: idx, f: fld, y: idx)
modifies rootAbs, root;
{
    assert mutatorTidWhole(tid) && rootAddr(x) && tidOwns(tid, x) && fieldAddr(f) && rootAddr(y) && tidOwns(tid, y) && memAddr(root[x]) && toAbs[root[x]] != nil && memAddrAbs(rootAbs[x]);
    rootAbs[y] := memAbs[rootAbs[x]][f];
    root[y] := mem[root[x]][f];
}

procedure {:yields} {:layer 99} {:refines "AtomicReadFieldRaw"} ReadFieldRaw({:linear "tid"} tid:Tid, x: idx, f: fld, y: idx)
{
    var valx: int;
    var valy: int;

    yield;
    call valx := ReadRoot(tid, x);
    call valy := ReadFieldGeneral(tid, valx, f);
    call WriteRoot(tid, y, valy);
    call SetRootAbs1(x, f, y);
    yield;
}

procedure {:atomic} {:layer 100} AtomicEqRaw({:linear "tid"} tid:Tid, x: idx, y:idx) returns (isEqual:bool)
{ assert mutatorTidWhole(tid) && rootAddr(x) && tidOwns(tid, x) && rootAddr(y) && tidOwns(tid, y); isEqual := root[x] == root[y]; }

procedure {:yields} {:layer 99} {:refines "AtomicEqRaw"} EqRaw({:linear "tid"} tid:Tid, x: idx, y:idx) returns (isEqual:bool)
{
    var vx:int;
    var vy:int;

    yield;
    call vx := ReadRoot(tid, x);
    call vy := ReadRoot(tid, y);
    isEqual := vx == vy;
    yield;
}

procedure {:atomic} {:layer 100} AtomicAllocRaw({:linear "tid"} tid:Tid, y:idx) returns (ptr: int, absPtr: obj)
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

procedure {:yields} {:layer 99} {:refines "AtomicAllocRaw"} AllocRaw({:linear "tid"} tid:Tid, y:idx) returns (ptr: int, absPtr: obj)
{
    yield;
    call absPtr := PrimitiveFindFreePtrAbs();
    call ptr := FindFreePtr(tid, absPtr);
    call WriteRoot(tid, y, ptr);
    call SetMemAbs2(absPtr);
    call SetRootAbs2(y, absPtr);
    yield;
}

procedure {:atomic} {:layer 99} AtomicFindFreePtr({:linear "tid"} tid: Tid, absPtr: obj) returns (ptr: int)
modifies Color, toAbs, mem;
{
    assert mutatorTidWhole(tid);
    assert (forall x: int, f: fld :: memAddr(x) && Unalloc(Color[x]) ==> toAbs[x] == nil);
    assume (memAddr(ptr) && Unalloc(Color[ptr]));
    Color[ptr] := if sweepPtr <= ptr then BLACK() else WHITE();
    toAbs[ptr] := absPtr;
    mem[ptr] := (lambda z: int :: if (fieldAddr(z)) then ptr else mem[ptr][z]);
}

procedure {:yields} {:layer 98} {:refines "AtomicFindFreePtr"} FindFreePtr({:linear "tid"} tid: Tid, absPtr: obj) returns (ptr: int)
{
    var iter: int;
    var spaceFound: bool;

    yield;
    spaceFound := false;
    while (true)
    invariant {:layer 98} !spaceFound;
    invariant {:layer 98} (forall x: int, f: fld :: memAddr(x) && Unalloc(Color[x]) ==> toAbs[x] == nil);
    {
        iter := memLo;
        while (iter < memHi)
        invariant {:layer 98} !spaceFound;
        invariant {:layer 98} memLo <= iter && iter <= memHi;
        invariant {:layer 98} memAddr(iter) && Unalloc(Color[iter]) ==> toAbs[iter] == nil;
        {
            call spaceFound := AllocIfPtrFree(tid, iter, absPtr);
            if (spaceFound)
            {
                ptr := iter;
                break;
            }
            else
            {
                iter := iter + 1;
            }
            yield;
        }
        if (spaceFound)
        {
            break;
        }
        yield;
    }
    yield;
}

procedure{:atomic} {:layer 100} AtomicWriteBarrier({:linear "tid"} tid:Tid, y:idx)
modifies Color;
{
    var val:int;
    assert mutatorTidWhole(tid) && rootAddr(y) && tidOwns(tid, y);
    val := root[y];
    if (MarkPhase(mutatorPhase[i#Tid(tid)]) && memAddr(val) && White(Color[val])) {
        Color[val] := GRAY();
    }
}

procedure{:yields} {:layer 99} {:refines "AtomicWriteBarrier"} WriteBarrier({:linear "tid"} tid:Tid, y:idx)
requires {:layer 98} mutatorTidWhole(tid);
{
    var phase: int;
    var rootVal: int;

    yield;
    assert {:layer 98} mutatorTidWhole(tid);
    call rootVal := ReadRoot(tid, y);
    if (memAddr(rootVal))
    {
        call phase := ReadMutatorPhase(tid);
      if (MarkPhase(phase))
        {
            call SET_InsertIntoSetIfWhiteByMutator(tid, rootVal);
        }
    }
    yield;
    assert {:layer 98} mutatorTidWhole(tid);
}

procedure {:atomic} {:layer 99} AtomicSET_InsertIntoSetIfWhiteByMutator({:linear "tid"} tid:Tid, memLocal:int)
modifies Color;
{
    assert mutatorTidWhole(tid) && memAddr(memLocal) && MarkPhase(mutatorPhase[i#Tid(tid)]);
    if (White(Color[memLocal])) {
        Color[memLocal] := GRAY();
    }
}

procedure {:yields} {:layer 98} {:refines "AtomicSET_InsertIntoSetIfWhiteByMutator"} SET_InsertIntoSetIfWhiteByMutator({:linear "tid"} tid:Tid, memLocal:int)
requires {:layer 98} mutatorTidWhole(tid) && MarkPhase(mutatorPhase[i#Tid(tid)]);
ensures {:layer 98} MarkPhase(mutatorPhase[i#Tid(tid)]);
{
    var color:int;

    yield;
    assert {:layer 98} mutatorTidWhole(tid) && MarkPhase(mutatorPhase[i#Tid(tid)]);
    assert {:layer 98} Color[memLocal] >= old(Color)[memLocal];

    call color := ReadColorByMutator3(tid, memLocal);
    if (!White(color))
    {
        yield;
        assert {:layer 98} mutatorTidWhole(tid) && MarkPhase(mutatorPhase[i#Tid(tid)]);
        assert {:layer 98} Color[memLocal] >= old(Color)[memLocal];
        return;
    }

    yield;
    assert {:layer 98} mutatorTidWhole(tid) && MarkPhase(mutatorPhase[i#Tid(tid)]);
    assert {:layer 98} Color[memLocal] >= old(Color)[memLocal];

    call MsPushByMutator(tid, memLocal);
    assert {:layer 98} MST(MarkStackPtr-1);
    yield;
    assert {:layer 98} mutatorTidWhole(tid) && MarkPhase(mutatorPhase[i#Tid(tid)]);
}

procedure {:left} {:layer 99} AtomicNoGrayInRootScanBarrier({:linear "tid"} tid:Tid) returns (noGray: bool)
{
        assert tid == GcTid && rootScanOn && mutatorsInRootScanBarrier == Mutators;
        noGray := (forall i: int :: memAddr(i) ==> !Gray(Color[i]));
}

procedure {:yields} {:layer 98} {:refines "AtomicNoGrayInRootScanBarrier"} NoGrayInRootScanBarrier({:linear "tid"} tid:Tid) returns (noGray: bool)
requires {:layer 98} tid == GcTid && MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
ensures {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
ensures {:layer 98} collectorPhase == old(collectorPhase);
{
    yield;
    assert {:layer 98} tid == GcTid;
    assert {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
    assert {:layer 98} collectorPhase == old(collectorPhase);
    call noGray := MsIsEmpty(tid);
    assert {:layer 98} noGray || MST(0);
    yield;
    assert {:layer 98} tid == GcTid;
    assert {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
    assert {:layer 98} collectorPhase == old(collectorPhase);
}

procedure {:left} {:layer 99} AtomicInsertIntoSetIfWhiteInRootScanBarrier({:linear "tid"} tid:Tid, memLocal:int)
modifies Color;
{
    assert tid == GcTid && rootScanOn && mutatorsInRootScanBarrier == Mutators && memAddr(memLocal);
    if (White(Color[memLocal])) {
        Color[memLocal] := GRAY();
    }
}

procedure {:yields} {:layer 98} {:refines "AtomicInsertIntoSetIfWhiteInRootScanBarrier"} InsertIntoSetIfWhiteInRootScanBarrier({:linear "tid"} tid:Tid, memLocal:int)
requires {:layer 98} tid == GcTid && MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
ensures {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
ensures {:layer 98} collectorPhase == old(collectorPhase);
{
    yield;
    assert {:layer 98} tid == GcTid;
    assert {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
    assert {:layer 98} collectorPhase == old(collectorPhase);
    call MsPushByCollector(tid, memLocal);
    assert {:layer 98} MST(MarkStackPtr-1);
    yield;
    assert {:layer 98} tid == GcTid;
    assert {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
    assert {:layer 98} collectorPhase == old(collectorPhase);
}

procedure {:left} {:layer 99,100} AtomicSET_InsertIntoSetIfWhite({:linear "tid"} tid:Tid, parent: int, child:int)
modifies Color;
{
    assert tid == GcTid;
    assert MarkPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase) && sweepPtr == memLo && memAddr(child);
    if (White(Color[child])) {
        Color[child] := GRAY();
    }
}

procedure {:yields} {:layer 98} {:refines "AtomicSET_InsertIntoSetIfWhite"} SET_InsertIntoSetIfWhite({:linear "tid"} tid:Tid, parent: int, child:int)
requires {:layer 98} tid == GcTid && memAddr(parent) && memAddr(child) && MsWellFormed(MarkStack, MarkStackPtr, Color, parent);
ensures {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, parent);
ensures {:layer 98} collectorPhase == old(collectorPhase);
{
    yield;
    assert {:layer 98} tid == GcTid && memAddr(parent) && memAddr(child);
    assert {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, parent);
    assert {:layer 98} collectorPhase == old(collectorPhase);
    call MsPushByCollector(tid, child);
    assert {:layer 98} MST(MarkStackPtr-1);
    yield;
    assert {:layer 98} tid == GcTid && memAddr(parent) && memAddr(child);
    assert {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, parent);
    assert {:layer 98} collectorPhase == old(collectorPhase);
}

procedure {:right} {:layer 99,100} AtomicSET_Peek({:linear "tid"} tid:Tid) returns (isEmpty: bool, val:int)
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

procedure {:yields} {:layer 98} {:refines "AtomicSET_Peek"} SET_Peek({:linear "tid"} tid:Tid) returns (isEmpty: bool, val:int)
requires {:layer 98} tid == GcTid && MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
ensures {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, if isEmpty then 0 else val);
ensures {:layer 98} collectorPhase == old(collectorPhase);
{
    yield;
    assert {:layer 98} tid == GcTid;
    assert {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, 0);
    assert {:layer 98} collectorPhase == old(collectorPhase);
    assert {:layer 98} MST(MarkStackPtr - 1);
    call isEmpty, val := MsPop(tid);
    yield;
    assert {:layer 98} tid == GcTid;
    assert {:layer 98} MsWellFormed(MarkStack, MarkStackPtr, Color, if isEmpty then 0 else val);
    assert {:layer 98} collectorPhase == old(collectorPhase);
}

//////////////////////////////////////////////////////////////////////////////
// Phase 96
//////////////////////////////////////////////////////////////////////////////

procedure {:atomic} {:layer 97,100} AtomicSET_RemoveFromSet({:linear "tid"} tid:Tid, scannedLocal:int)
modifies Color;
{
    assert MarkPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase);
    assert tid == GcTid;
    assert memAddr(scannedLocal);
    Color[scannedLocal] := BLACK();
}

procedure {:yields} {:layer 96} {:refines "AtomicSET_RemoveFromSet"} SET_RemoveFromSet({:linear "tid"} tid:Tid, scannedLocal:int)
{
    yield;
    call LockAcquire(tid);
    call SetColor2(tid, scannedLocal, BLACK());
    call LockRelease(tid);
    yield;
}

procedure {:atomic} {:layer 97,98} AtomicMsPushByCollector({:linear "tid"} tid: Tid, val: int)
modifies Color, MarkStack, MarkStackPtr;
{
    assert memAddr(val) && tid == GcTid;
    if (White(Color[val])) {
        Color[val] := GRAY();
        MarkStack[MarkStackPtr] := val;
        MarkStackPtr := MarkStackPtr + 1;
    }
}

procedure {:yields} {:layer 96} {:refines "AtomicMsPushByCollector"} MsPushByCollector({:linear "tid"} tid: Tid, val: int)
{
    var color:int;
    var stack:int;
    yield;
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
    yield;
}

procedure {:atomic} {:layer 97,98} AtomicMsPushByMutator({:linear "tid"} tid: Tid, val: int)
modifies Color, MarkStack, MarkStackPtr;
{
    assert memAddr(val) && mutatorTidWhole(tid) && MarkPhase(mutatorPhase[i#Tid(tid)]);
    if (White(Color[val])) {
        Color[val] := GRAY();
        MarkStack[MarkStackPtr] := val;
        MarkStackPtr := MarkStackPtr + 1;
    }
}

procedure {:yields} {:layer 96} {:refines "AtomicMsPushByMutator"} MsPushByMutator({:linear "tid"} tid: Tid, val: int)
{
    var color:int;
    var stack:int;
    yield;
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
    yield;
}

procedure{:atomic} {:layer 97,98} AtomicMsPop({:linear "tid"} tid:Tid) returns (isEmpty: bool, val:int)
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

procedure{:yields} {:layer 96} {:refines "AtomicMsPop"} MsPop({:linear "tid"} tid:Tid) returns (isEmpty: bool, val:int)
{
    var stack:int;
    yield;
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
    yield;
}

procedure{:atomic} {:layer 97,98} AtomicMsIsEmpty({:linear "tid"} tid: Tid) returns (isEmpty: bool)
{ assert tid == GcTid; isEmpty := MarkStackPtr == 0; }

procedure{:yields} {:layer 96} {:refines "AtomicMsIsEmpty"} MsIsEmpty({:linear "tid"} tid: Tid) returns (isEmpty: bool)
{
    var v:int;
    yield;
    call LockAcquire(tid);
    call v := ReadMarkStackPtr(tid);
    isEmpty := v == 0;
    call LockRelease(tid);
    yield;
}

procedure {:atomic} {:layer 97,100} AtomicResetSweepPtr({:linear "tid"} tid:Tid)
modifies sweepPtr;
{ assert tid == GcTid; sweepPtr := memLo; }

procedure {:yields} {:layer 96} {:refines "AtomicResetSweepPtr"} ResetSweepPtr({:linear "tid"} tid:Tid)
{
    yield;
    call LockAcquire(tid);
    call SetSweepPtrLocked(tid, memLo);
    call LockRelease(tid);
    yield;
}

procedure {:left} {:layer 97,100} AtomicSweepNext({:linear "tid"} tid:Tid)
modifies Color, sweepPtr;
{
    assert SweepPhase(collectorPhase) && PhaseConsistent(collectorPhase, mutatorPhase);
    assert !Gray(Color[sweepPtr]);
    assert tid == GcTid;
    assert memAddr(sweepPtr);
    Color[sweepPtr] := if White(Color[sweepPtr]) then UNALLOC() else if Black(Color[sweepPtr]) then WHITE() else Color[sweepPtr];
    sweepPtr := sweepPtr + 1;
}

procedure {:yields} {:layer 96} {:refines "AtomicSweepNext"} SweepNext({:linear "tid"} tid:Tid)
{
    var color:int;
    var sweep:int;
    yield;
    call LockAcquire(tid);
    call sweep := ReadSweepPtr(tid);
    call color := ReadColorByCollector(tid, sweep);
    color := if White(color) then UNALLOC() else if Black(color) then WHITE() else color;
    call SetColor(tid, sweep, color);
    sweep := sweep + 1;
    call SetSweepPtrLocked(tid, sweep);
    call LockRelease(tid);
    yield;
}

procedure{:atomic} {:layer 97,100} AtomicHandshakeCollector({:linear "tid"} tid:Tid) returns (nextPhase: int)
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

procedure{:yields} {:layer 96} {:refines "AtomicHandshakeCollector"} HandshakeCollector({:linear "tid"} tid:Tid) returns (nextPhase: int)
{
    var phase:int;
    yield;
    call LockAcquire(tid);
    call phase := ReadCollectorPhase(tid);
    nextPhase := if IdlePhase(phase) then MARK() else if MarkPhase(phase) then SWEEP() else IDLE();
    call SetCollectorPhase(tid, nextPhase);
    call LockRelease(tid);
    yield;
}

procedure {:atomic} {:layer 97,100} AtomicUpdateMutatorPhase({:linear "tid"} tid: Tid)
modifies mutatorPhase;
{ assert mutatorTidWhole(tid); mutatorPhase[i#Tid(tid)] := collectorPhase; }

procedure {:yields} {:layer 96} {:refines "AtomicUpdateMutatorPhase"} UpdateMutatorPhase({:linear "tid"} tid: Tid)
{
    var p:int;
    yield;
    call LockAcquire(tid);
    call p := ReadCollectorPhaseLocked(tid);
    call SetMutatorPhaseLocked(tid, p);
    call LockRelease(tid);
    yield;
}

procedure {:atomic} {:layer 97,99} AtomicCollectorRootScanBarrierStart({:linear "tid"} tid: Tid)
modifies rootScanOn;
{ assert tid == GcTid; rootScanOn := true; }

procedure {:yields} {:layer 96} {:refines "AtomicCollectorRootScanBarrierStart"} CollectorRootScanBarrierStart({:linear "tid"} tid: Tid)
{
    yield;
    call LockAcquire(tid);
    call CollectorRootScanBarrierStartLocked(tid);
    call LockRelease(tid);
    yield;
}

procedure {:left} {:layer 97,99} AtomicCollectorRootScanBarrierEnd({:linear "tid"} tid: Tid)
modifies rootScanOn;
{ assert tid == GcTid; rootScanOn := false; }

procedure {:yields} {:layer 96} {:refines "AtomicCollectorRootScanBarrierEnd"} CollectorRootScanBarrierEnd({:linear "tid"} tid: Tid)
{
    yield;
    call LockAcquire(tid);
    call CollectorRootScanBarrierEndLocked(tid);
    call LockRelease(tid);
    yield;
}

procedure {:atomic} {:layer 97,99} AtomicCollectorRootScanBarrierWait({:linear "tid"} tid: Tid)
{ assert tid == GcTid; assume rootScanBarrier == 0; }

procedure {:yields} {:layer 96} {:refines "AtomicCollectorRootScanBarrierWait"} CollectorRootScanBarrierWait({:linear "tid"} tid: Tid)
{
    var v:int;

    yield;
    while (true)
    {
        yield;
        call v := CollectorRootScanBarrierRead(tid);
        yield;
        if (v == 0)
        {
            yield;
            return;
        }
    }
    yield;
}

procedure {:atomic} {:layer 97,99} AtomicMutatorRootScanBarrierEnter({:linear_in "tid"} tid: Tid) returns({:linear "tid"} tid_left: Tid)
modifies rootScanBarrier, mutatorsInRootScanBarrier;
{
                        assert mutatorTidWhole(tid);
                        rootScanBarrier := rootScanBarrier - 1;
                        mutatorsInRootScanBarrier[i#Tid(tid)] := true;
                        tid_left := Tid(i#Tid(tid), true, false);
}

procedure {:yields} {:layer 96} {:refines "AtomicMutatorRootScanBarrierEnter"} MutatorRootScanBarrierEnter({:linear_in "tid"} tid: Tid) returns({:linear "tid"} tid_left: Tid)
requires {:layer 95} mutatorTidWhole(tid);
ensures {:layer 95,96} i#Tid(tid_left) == i#Tid(tid) && left#Tid(tid_left);
{
    var{:linear "tid"} tid_right: Tid;

    yield;
    call tid_left, tid_right := TidSplit(tid);
    call LockAcquire(tid_left);
    call MutatorsInRootScanBarrierAdd(tid_left, tid_right);
    call AddRootScanBarrier(tid_left, -1);
    call LockRelease(tid_left);
    yield;
}

procedure {:atomic} {:layer 97,99} AtomicMutatorRootScanBarrierWait({:linear_in "tid"} tid_left: Tid) returns({:linear "tid"} tid: Tid)
modifies rootScanBarrier, mutatorsInRootScanBarrier;
{
                        assert mutatorTidLeft(tid_left) && mutatorsInRootScanBarrier[i#Tid(tid_left)];
                        assume !rootScanOn;
                        rootScanBarrier := rootScanBarrier + 1;
                        mutatorsInRootScanBarrier[i#Tid(tid_left)] := false;
                        tid := Tid(i#Tid(tid_left), true, true);
}

procedure {:yields} {:layer 96} {:refines "AtomicMutatorRootScanBarrierWait"} MutatorRootScanBarrierWait({:linear_in "tid"} tid_left: Tid) returns({:linear "tid"} tid: Tid)
ensures {:layer 95,96} i#Tid(tid) == i#Tid(tid_left) && left#Tid(tid) && right#Tid(tid);
{
    var{:linear "tid"} tid_right: Tid;
    var b:bool;

    yield;
    loop:
        yield;
        call LockAcquire(tid_left);
        call b := MutatorReadBarrierOn(tid_left);
        if (!b)
        {
            call AddRootScanBarrier(tid_left, 1);
            call tid_right := MutatorsInRootScanBarrierRemove(tid_left);
            call LockRelease(tid_left);
            call tid := TidCombine(tid_left, tid_right);
            yield;
            return;
        }
        call LockRelease(tid_left);
        yield;
        goto loop;
}

procedure {:atomic} {:layer 97,98} AtomicAllocIfPtrFree({:linear "tid"} tid:Tid, ptr:int, absPtr:obj) returns (spaceFound:bool)
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

procedure {:yields} {:layer 96} {:refines "AtomicAllocIfPtrFree"} AllocIfPtrFree({:linear "tid"} tid:Tid, ptr:int, absPtr:obj) returns (spaceFound:bool)
{
    var color:int;
    var sweep:int;
    var t:[int]obj;
    var fldIter:fld;
    var {:layer 96} snapMem: [int][fld]int;

    yield;
    call color := ReadColorByMutator1(tid, ptr);
    if (Unalloc(color))
    {
        yield;
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
            invariant {:layer 96} 0 <= fldIter && fldIter <= numFields;
          invariant {:layer 96} mem == snapMem[ptr := (lambda z: int :: if (0 <= z && z < fldIter) then ptr else snapMem[ptr][z])];
            {
                call InitializeFieldInAlloc(tid, ptr, fldIter);
    fldIter := fldIter + 1;
            }

            call SetColor3(tid, ptr, color, absPtr);
            call LockRelease(tid);
            yield;
            return;
        }
        call LockRelease(tid);
    }
    spaceFound := false;
    yield;
}

procedure {:atomic} {:layer 97,100} AtomicIsWhiteByCollector({:linear "tid"} tid:Tid, i: int) returns (isWhite: bool)
{ assert tid == GcTid && memAddr(i); isWhite := White(Color[i]); }

procedure {:yields} {:layer 96} {:refines "AtomicIsWhiteByCollector"} IsWhiteByCollector({:linear "tid"} tid:Tid, i: int) returns (isWhite: bool)
{
    var v:int;
    yield;
    call LockAcquire(tid);
    call v := ReadColorByCollector(tid, i);
    isWhite := White(v);
    call LockRelease(tid);
    yield;
}

procedure {:atomic} {:layer 97,100} AtomicClearToAbsWhite({:linear "tid"} tid:Tid)
modifies toAbs;
{ assert tid == GcTid; toAbs := (lambda x: int :: if memAddr(x) && White(Color[x]) then nil else toAbs[x]); }

procedure {:yields} {:layer 96} {:refines "AtomicClearToAbsWhite"} ClearToAbsWhite({:linear "tid"} tid:Tid)
{
    yield;
    call LockAcquire(tid);
    call LockedClearToAbsWhite(tid);
    call LockRelease(tid);
    yield;
}

//////////////////////////////////////////////////////////////////////////////
// Phase 95
//////////////////////////////////////////////////////////////////////////////

procedure {:atomic} {:layer 96} AtomicLockedClearToAbsWhite({:linear "tid"} tid:Tid)
modifies toAbs;
{ assert tid == GcTid && tidHasLock(tid, lock); toAbs := (lambda x: int :: if memAddr(x) && White(Color[x]) then nil else toAbs[x]); }

procedure {:yields} {:layer 95} {:refines "AtomicLockedClearToAbsWhite"} LockedClearToAbsWhite({:linear "tid"} tid:Tid)
{
    yield;
    call SetToAbs1();
    yield;
}

procedure {:both} {:layer 96,99} AtomicInitField({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool, x: int, f: int)
modifies mem;
{ assert gcAndMutatorTids(tid, mutatorTids) && memAddr(x) && fieldAddr(f); mem[x][f] := x; }

procedure {:yields} {:layer 95} {:refines "AtomicInitField"} InitField({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool, x: int, f: int)
{
    yield;
    call PrimitiveWriteField(x, f, x);
    yield;
}

procedure {:atomic} {:layer 96,100} AtomicReadFieldCollector({:linear "tid"} tid:Tid, x:int, f: fld) returns (y: int)
{ assert tid == GcTid && memAddr(x) && fieldAddr(f) && toAbs[x] != nil; y := mem[x][f]; }

procedure {:yields} {:layer 95} {:refines "AtomicReadFieldCollector"} ReadFieldCollector({:linear "tid"} tid:Tid, x:int, f: fld) returns (y: int)
{
    yield;
    call y := PrimitiveReadField(x, f);
    yield;
}

procedure {:atomic} {:layer 96,99} AtomicReadFieldGeneral({:linear "tid"} tid:Tid, x: int, f: fld) returns (y: int)
{ assert mutatorTidWhole(tid) && memAddr(x) && fieldAddr(f) && toAbs[x] != nil; y := mem[x][f]; }

procedure {:yields} {:layer 95} {:refines "AtomicReadFieldGeneral"} ReadFieldGeneral({:linear "tid"} tid:Tid, x: int, f: fld) returns (y: int)
{
    yield;
    call y := PrimitiveReadField(x, f);
    yield;
}

procedure {:atomic} {:layer 96,99} AtomicWriteFieldGeneral({:linear "tid"} tid:Tid, x: int, f: fld, y: int)
modifies mem;
{ assert mutatorTidWhole(tid) && memAddr(x) && fieldAddr(f) && toAbs[x] != nil; mem[x][f] := y; }

procedure {:yields} {:layer 95} {:refines "AtomicWriteFieldGeneral"} WriteFieldGeneral({:linear "tid"} tid:Tid, x: int, f: fld, y: int)
{
    yield;
    call PrimitiveWriteField(x, f, y);
    yield;
}

procedure {:right} {:layer 96} AtomicInitializeFieldInAlloc({:linear "tid"} tid: Tid, ptr: int, fld: int)
modifies mem;
{ assert mutatorTidWhole(tid) && tidHasLock(tid, lock) && memAddr(ptr) && fieldAddr(fld) && toAbs[ptr] == nil; mem[ptr][fld] := ptr; }

procedure {:yields} {:layer 95} {:refines "AtomicInitializeFieldInAlloc"} InitializeFieldInAlloc({:linear "tid"} tid: Tid, ptr: int, fld: int)
{
    yield;
    call PrimitiveWriteField(ptr, fld, ptr);
    yield;
}

procedure{:both} {:layer 96} AtomicReadMarkStackPtr({:linear "tid"} tid:Tid) returns (val: int)
{ assert tidHasLock(tid, lock); val := MarkStackPtr; }

procedure{:yields} {:layer 95} {:refines "AtomicReadMarkStackPtr"} ReadMarkStackPtr({:linear "tid"} tid:Tid) returns (val: int)
{
    yield;
    call val := PrimitiveReadMarkStackPtr();
    yield;
}

procedure{:atomic} {:layer 96,98} AtomicInitMarkStackPtr({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool)
modifies MarkStackPtr;
{ assert gcAndMutatorTids(tid, mutatorTids); MarkStackPtr := 0; }

procedure{:yields} {:layer 95} {:refines "AtomicInitMarkStackPtr"} InitMarkStackPtr({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool)
{
    yield;
    call PrimitiveSetMarkStackPtr(0);
    yield;
}

procedure{:both} {:layer 96} AtomicSetMarkStackPtr({:linear "tid"} tid:Tid, val: int)
modifies MarkStackPtr;
{ assert tidHasLock(tid, lock); MarkStackPtr := val; }

procedure{:yields} {:layer 95} {:refines "AtomicSetMarkStackPtr"} SetMarkStackPtr({:linear "tid"} tid:Tid, val: int)
{
    yield;
    call PrimitiveSetMarkStackPtr(val);
    yield;
}

procedure{:both} {:layer 96} AtomicReadMarkStack({:linear "tid"} tid:Tid, ptr: int) returns(val: int)
{ assert tidHasLock(tid, lock); val := MarkStack[ptr]; }

procedure{:yields} {:layer 95} {:refines "AtomicReadMarkStack"} ReadMarkStack({:linear "tid"} tid:Tid, ptr: int) returns(val: int)
{
    yield;
    call val := PrimitiveReadMarkStack(ptr);
    yield;
}

procedure{:both} {:layer 96} AtomicWriteMarkStack({:linear "tid"} tid:Tid, ptr: int, val: int)
modifies MarkStack;
{ assert tidHasLock(tid, lock); MarkStack[ptr] := val; }

procedure{:yields} {:layer 95} {:refines "AtomicWriteMarkStack"} WriteMarkStack({:linear "tid"} tid:Tid, ptr: int, val: int)
{
    yield;
    call PrimitiveWriteMarkStack(ptr, val);
    yield;
}

procedure {:both} {:layer 96,99} AtomicInitCollectorPhase({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool)
modifies collectorPhase;
{ assert gcAndMutatorTids(tid, mutatorTids); collectorPhase := IDLE(); }

procedure {:yields} {:layer 95} {:refines "AtomicInitCollectorPhase"} InitCollectorPhase({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool)
{
    yield;
    call PrimitiveSetCollectorPhase(IDLE());
    yield;
}

procedure {:atomic} {:layer 96} AtomicReadCollectorPhase({:linear "tid"} tid: Tid) returns (phase:int)
{ assert tid == GcTid; phase := collectorPhase; }

procedure {:yields} {:layer 95} {:refines "AtomicReadCollectorPhase"} ReadCollectorPhase({:linear "tid"} tid: Tid) returns (phase:int)
{
    yield;
    call phase := PrimitiveReadCollectorPhase();
    yield;
}

procedure {:right} {:layer 96} AtomicReadCollectorPhaseLocked({:linear "tid"} tid: Tid) returns (phase:int)
{ assert mutatorTidWhole(tid) && tidHasLock(tid, lock); phase := collectorPhase; }

procedure {:yields} {:layer 95} {:refines "AtomicReadCollectorPhaseLocked"} ReadCollectorPhaseLocked({:linear "tid"} tid: Tid) returns (phase:int)
{
    yield;
    call phase := PrimitiveReadCollectorPhase();
    yield;
}

procedure {:both} {:layer 96} AtomicSetCollectorPhase({:linear "tid"} tid: Tid, phase:int)
modifies collectorPhase;
{ assert tid == GcTid && tidHasLock(tid, lock); collectorPhase := phase; }

procedure {:yields} {:layer 95} {:refines "AtomicSetCollectorPhase"} SetCollectorPhase({:linear "tid"} tid: Tid, phase:int)
{
    yield;
    call PrimitiveSetCollectorPhase(phase);
    yield;
}

procedure {:both} {:layer 96,99} AtomicInitMutatorPhase({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool, id: int)
modifies mutatorPhase;
{ assert gcAndMutatorTids(tid, mutatorTids); mutatorPhase[id] := IDLE(); }

procedure {:yields} {:layer 95} {:refines "AtomicInitMutatorPhase"} InitMutatorPhase({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool, id: int)
{
    yield;
    call PrimitiveSetMutatorPhase(id, IDLE());
    yield;
}

procedure {:atomic} {:layer 96,100} AtomicReadMutatorPhaseByCollector({:linear "tid"} tid: Tid, i: int) returns (phase:int)
{ assert tid == GcTid; phase := mutatorPhase[i]; }

procedure {:yields} {:layer 95} {:refines "AtomicReadMutatorPhaseByCollector"} ReadMutatorPhaseByCollector({:linear "tid"} tid: Tid, i: int) returns (phase:int)
{
    yield;
    call phase := PrimitiveReadMutatorPhase(i);
    yield;
}

procedure {:both} {:layer 96,99} AtomicReadMutatorPhase({:linear "tid"} tid: Tid) returns (phase:int)
{ assert mutatorTidWhole(tid); phase := mutatorPhase[i#Tid(tid)]; }

procedure {:yields} {:layer 95} {:refines "AtomicReadMutatorPhase"} ReadMutatorPhase({:linear "tid"} tid: Tid) returns (phase:int)
{
    yield;
    call phase := PrimitiveReadMutatorPhase(i#Tid(tid));
    yield;
}

procedure {:atomic} {:layer 96} AtomicSetMutatorPhaseLocked({:linear "tid"} tid: Tid, phase: int)
modifies mutatorPhase;
{ assert mutatorTidWhole(tid) && tidHasLock(tid, lock) && phase == collectorPhase; mutatorPhase[i#Tid(tid)] := phase; }

procedure {:yields} {:layer 95} {:refines "AtomicSetMutatorPhaseLocked"} SetMutatorPhaseLocked({:linear "tid"} tid: Tid, phase: int)
{
    yield;
    call PrimitiveSetMutatorPhase(i#Tid(tid), phase);
    yield;
}

procedure {:both} {:layer 96,99} AtomicInitSweepPtr({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool)
modifies sweepPtr;
{ assert gcAndMutatorTids(tid, mutatorTids); sweepPtr := memHi; }

procedure {:yields} {:layer 95} {:refines "AtomicInitSweepPtr"} InitSweepPtr({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool)
{
    yield;
    call PrimitiveSetSweepPtr(memHi);
    yield;
}

procedure {:both} {:layer 96} AtomicReadSweepPtr({:linear "tid"} tid:Tid) returns(val:int)
{ assert tidHasLock(tid, lock); val := sweepPtr; }

procedure {:yields} {:layer 95} {:refines "AtomicReadSweepPtr"} ReadSweepPtr({:linear "tid"} tid:Tid) returns(val:int)
{
    yield;
    call val := PrimitiveReadSweepPtr();
    yield;
}

procedure {:atomic} {:layer 96} AtomicSetSweepPtrLocked({:linear "tid"} tid:Tid, val: int)
modifies sweepPtr;
{ assert tid == GcTid && tidHasLock(tid, lock); sweepPtr := val; }

procedure {:yields} {:layer 95} {:refines "AtomicSetSweepPtrLocked"} SetSweepPtrLocked({:linear "tid"} tid:Tid, val: int)
{
    yield;
    call PrimitiveSetSweepPtr(val);
    yield;
}

procedure {:atomic} {:layer 96} AtomicCollectorRootScanBarrierStartLocked({:linear "tid"} tid: Tid)
modifies rootScanOn;
{ assert tid == GcTid && tidHasLock(tid, lock); rootScanOn := true; }

procedure {:yields} {:layer 95} {:refines "AtomicCollectorRootScanBarrierStartLocked"} CollectorRootScanBarrierStartLocked({:linear "tid"} tid: Tid)
{
    yield;
    call PrimitiveSetRootScanOn(true);
    yield;
}

procedure {:atomic} {:layer 96} AtomicCollectorRootScanBarrierEndLocked({:linear "tid"} tid: Tid)
modifies rootScanOn;
{ assert tid == GcTid && tidHasLock(tid, lock); rootScanOn := false; }

procedure {:yields} {:layer 95} {:refines "AtomicCollectorRootScanBarrierEndLocked"} CollectorRootScanBarrierEndLocked({:linear "tid"} tid: Tid)
{
    yield;
    call PrimitiveSetRootScanOn(false);
    yield;
}

procedure {:right} {:layer 96} AtomicMutatorReadBarrierOn({:linear "tid"} tid: Tid) returns (val:bool)
{ assert tidHasLock(tid, lock); val := rootScanOn; }

procedure {:yields} {:layer 95} {:refines "AtomicMutatorReadBarrierOn"} MutatorReadBarrierOn({:linear "tid"} tid: Tid) returns (val:bool)
{
    yield;
    call val := PrimitiveReadRootScanOn();
    yield;
}

procedure {:yields} {:layer 95} PollMutatorReadBarrierOn({:linear "tid"} tid: Tid) returns (val:bool)
{
    yield;
    call val := PrimitiveReadRootScanOn();
    yield;
}

procedure{:atomic} {:layer 96,99} AtomicInitRootScanBarrier({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool)
modifies rootScanBarrier;
{ assert gcAndMutatorTids(tid, mutatorTids); rootScanBarrier := numMutators; }

procedure{:yields} {:layer 95} {:refines "AtomicInitRootScanBarrier"} InitRootScanBarrier({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool)
{
    yield;
    call PrimitiveSetRootScanBarrier(numMutators);
    yield;
}

procedure {:atomic} {:layer 96} AtomicCollectorRootScanBarrierRead({:linear "tid"} tid: Tid) returns (val:int)
{ assert tid == GcTid; val := rootScanBarrier; }

procedure {:yields} {:layer 95} {:refines "AtomicCollectorRootScanBarrierRead"} CollectorRootScanBarrierRead({:linear "tid"} tid: Tid) returns (val:int)
{
    yield;
    call val := PrimitiveReadRootScanBarrier();
    yield;
}

procedure {:atomic} {:layer 96} AtomicAddRootScanBarrier({:linear "tid"} tid_left: Tid, val: int)
modifies rootScanBarrier;
{ assert mutatorTidLeft(tid_left) && tidHasLock(tid_left, lock); rootScanBarrier := rootScanBarrier + val; }

procedure {:yields} {:layer 95} {:refines "AtomicAddRootScanBarrier"} AddRootScanBarrier({:linear "tid"} tid_left: Tid, val: int)
{
    yield;
    call PrimitiveAddRootScanBarrier(val);
    yield;
}

procedure {:right} {:layer 96} AtomicMutatorsInRootScanBarrierAdd({:linear "tid"} tid_left: Tid, {:linear_in "tid"} tid_right: Tid)
modifies mutatorsInRootScanBarrier;
{
    assert tidHasLock(tid_left, lock) && mutatorTidRight(tid_right);
    mutatorsInRootScanBarrier[i#Tid(tid_right)] := true;
}

procedure {:yields} {:layer 95} {:refines "AtomicMutatorsInRootScanBarrierAdd"} MutatorsInRootScanBarrierAdd({:linear "tid"} tid_left: Tid, {:linear_in "tid"} tid_right: Tid)
{
    yield;
    call PrimitiveMutatorsInRootScanBarrierAdd(tid_right);
    yield;
}

procedure {:both} {:layer 96} AtomicMutatorsInRootScanBarrierRemove({:linear "tid"} tid_left: Tid) returns({:linear "tid"} tid_right: Tid)
modifies mutatorsInRootScanBarrier;
{
    assert tidHasLock(tid_left, lock) && !rootScanOn && mutatorTidLeft(tid_left) && mutatorsInRootScanBarrier[i#Tid(tid_left)];
    mutatorsInRootScanBarrier[i#Tid(tid_left)] := false;
    tid_right := Tid(i#Tid(tid_left), false, true);
}

procedure {:yields} {:layer 95} {:refines "AtomicMutatorsInRootScanBarrierRemove"} MutatorsInRootScanBarrierRemove({:linear "tid"} tid_left: Tid) returns({:linear "tid"} tid_right: Tid)
ensures {:layer 95} i#Tid(tid_left) == i#Tid(tid_right);
ensures {:layer 95} left#Tid(tid_left) && right#Tid(tid_right);
{
    yield;
    call tid_right := PrimitiveMutatorsInRootScanBarrierRemove(tid_left);
    yield;
}

procedure {:both} {:layer 96,99} AtomicInitRoot({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool, x: int)
modifies root;
{ assert gcAndMutatorTids(tid, mutatorTids) && rootAddr(x); root[x] := 0; }

procedure {:yields} {:layer 95} {:refines "AtomicInitRoot"} InitRoot({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool, x: int)
{
    yield;
    call PrimitiveWriteRoot(x, 0);
    yield;
}

procedure {:left} {:layer 96,99} AtomicReadRootInRootScanBarrier({:linear "tid"} tid:Tid, x: idx) returns (val: int)
{ assert tid == GcTid && rootAddr(x) && rootScanOn && mutatorsInRootScanBarrier == Mutators; val := root[x]; }

procedure {:yields} {:layer 95} {:refines "AtomicReadRootInRootScanBarrier"} ReadRootInRootScanBarrier({:linear "tid"} tid:Tid, x: idx) returns (val: int)
{
    yield;
    call val := PrimitiveReadRoot(x);
    yield;
}

procedure {:both} {:layer 96,99} AtomicWriteRoot({:linear "tid"} tid: Tid, i: idx, val: int)
modifies root;
{ assert mutatorTidWhole(tid) && rootAddr(i) && tidOwns(tid, i); root[i] := val; }

procedure {:yields} {:layer 95} {:refines "AtomicWriteRoot"} WriteRoot({:linear "tid"} tid: Tid, i: idx, val: int)
{
    yield;
    call PrimitiveWriteRoot(i, val);
    yield;
}

procedure {:both} {:layer 96,99} AtomicReadRoot({:linear "tid"} tid: Tid, i: idx) returns (val: int)
{ assert mutatorTidWhole(tid) && rootAddr(i) && tidOwns(tid, i); val := root[i]; }

procedure {:yields} {:layer 95} {:refines "AtomicReadRoot"} ReadRoot({:linear "tid"} tid: Tid, i: idx) returns (val: int)
{
    yield;
    call val := PrimitiveReadRoot(i);
    yield;
}

procedure {:both} {:layer 96,99} AtomicInitColor({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool, x: int)
modifies Color;
{ assert gcAndMutatorTids(tid, mutatorTids) && memAddr(x); Color[x] := UNALLOC(); }

procedure {:yields} {:layer 95} {:refines "AtomicInitColor"} InitColor({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool, x: int)
{
    yield;
    call PrimitiveSetColor(x, UNALLOC());
    yield;
}

procedure {:both} {:layer 96} AtomicReadColorByCollector({:linear "tid"} tid:Tid, i: int) returns (val: int)
{ assert tid == GcTid && tidHasLock(tid, lock) && memAddr(i); val := Color[i]; }

procedure {:yields} {:layer 95} {:refines "AtomicReadColorByCollector"} ReadColorByCollector({:linear "tid"} tid:Tid, i: int) returns (val: int)
{
    yield;
    call val := PrimitiveReadColor(i);
    yield;
}

procedure {:atomic} {:layer 96} AtomicReadColorByMutator1({:linear "tid"} tid:Tid, i: int) returns (val: int)
{ assert mutatorTidWhole(tid) && memAddr(i); }

procedure {:yields} {:layer 95} {:refines "AtomicReadColorByMutator1"} ReadColorByMutator1({:linear "tid"} tid:Tid, i: int) returns (val: int)
{
    yield;
    call val := PrimitiveReadColor(i);
    yield;
}

procedure {:both} {:layer 96} AtomicReadColorByMutator2({:linear "tid"} tid:Tid, i: int) returns (val: int)
{ assert mutatorTidWhole(tid) && tidHasLock(tid, lock) && memAddr(i); val := Color[i]; }

procedure {:yields} {:layer 95} {:refines "AtomicReadColorByMutator2"} ReadColorByMutator2({:linear "tid"} tid:Tid, i: int) returns (val: int)
{
    yield;
    call val := PrimitiveReadColor(i);
    yield;
}

procedure {:atomic} {:layer 96,98} AtomicReadColorByMutator3({:linear "tid"} tid:Tid, i: int) returns (val: int)
{
    assert mutatorTidWhole(tid) && memAddr(i) && MarkPhase(mutatorPhase[i#Tid(tid)]);
    assume White(Color[i]) ==> White(val);
}

procedure {:yields} {:layer 95} {:refines "AtomicReadColorByMutator3"} ReadColorByMutator3({:linear "tid"} tid:Tid, i: int) returns (val: int)
{
    yield;
    call val := PrimitiveReadColor(i);
    yield;
}

procedure {:both} {:layer 96} AtomicSetColor({:linear "tid"} tid:Tid, i: int, val: int)
modifies Color;
{ assert tidHasLock(tid, lock) && memAddr(i) && PhaseConsistent(collectorPhase, mutatorPhase) && !MarkPhase(collectorPhase); Color[i] := val; }

procedure {:yields} {:layer 95} {:refines "AtomicSetColor"} SetColor({:linear "tid"} tid:Tid, i: int, val: int)
{
    yield;
    call PrimitiveSetColor(i, val);
    yield;
}

procedure {:left} {:layer 96} AtomicSetColor2({:linear "tid"} tid:Tid, i: int, val: int)
modifies Color;
{
    assert tidHasLock(tid, lock) && memAddr(i);
    assert (MarkPhase(collectorPhase) || !PhaseConsistent(collectorPhase, mutatorPhase) ==> !White(val));
    Color[i] := val;
}

procedure {:yields} {:layer 95} {:refines "AtomicSetColor2"} SetColor2({:linear "tid"} tid:Tid, i: int, val: int)
{
    yield;
    call PrimitiveSetColor(i, val);
    yield;
}

procedure {:atomic} {:layer 96} AtomicSetColor3({:linear "tid"} tid:Tid, i: int, val: int, o: obj)
modifies Color, toAbs;
{
    assert tidHasLock(tid, lock) && memAddr(i);
    assert White(val) ==> Unalloc(Color[i]);
    Color[i] := val;
    toAbs[i] := o;
}

procedure {:yields} {:layer 95} {:refines "AtomicSetColor3"} SetColor3({:linear "tid"} tid:Tid, i: int, val: int, o: obj)
{
    yield;
    call PrimitiveSetColor(i, val);
    call SetToAbs2(i, o);
    yield;
}

procedure {:both} {:layer 96,99} AtomicInitToAbs({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool)
modifies toAbs;
{
  assert gcAndMutatorTids(tid, mutatorTids);
  toAbs := (lambda i:int :: if memAddr(i) then nil else Int(i));
}

procedure {:yields} {:layer 95} {:refines "AtomicInitToAbs"} InitToAbs({:linear "tid"} tid:Tid, {:linear "tid"} mutatorTids:[int]bool)
{
    yield;
    call SetToAbs3();
    yield;
}

procedure {:right} {:layer 96} AtomicLockAcquire({:linear "tid"} tid: Tid)
modifies lock;
{ assert i#Tid(tid) != 0; assume lock == 0; lock := i#Tid(tid); }

procedure {:yields} {:layer 95} {:refines "AtomicLockAcquire"} LockAcquire({:linear "tid"} tid: Tid)
{
    var status:bool;
    yield;
    while (true)
    {
        call status := PrimitiveLockCAS(i#Tid(tid));
        if (status)
        {
            yield;
            return;
        }
        yield;
    }
    yield;
}

procedure {:left} {:layer 96} AtomicLockRelease({:linear "tid"} tid:Tid)
modifies lock;
{ assert tidHasLock(tid, lock); lock := 0; }

procedure {:yields} {:layer 95} {:refines "AtomicLockRelease"} LockRelease({:linear "tid"} tid:Tid)
{
    yield;
    call PrimitiveLockZero();
    yield;
}

procedure {:layer 96} {:inline 1} GhostReadMem() returns (snapMem: [int][fld]int)
{
    snapMem := mem;
}

procedure {:layer 99} {:inline 1} GhostReadColor99() returns (snapColor: [int]int)
{
    snapColor := Color;
}

procedure {:layer 100} {:inline 1} GhostReadColor100() returns (snapColor: [int]int)
{
    snapColor := Color;
}

//////////////////////////////////////////////////////////////////////////////
// ATOMIC PRIMITIVES
//   The action specifications, linearity specifications, and requires/ensures below here are trusted.
//   (Note, though, that Boogie still verifies the mover types (atomic,left,right,both); these are not trusted.)
//////////////////////////////////////////////////////////////////////////////

procedure {:both} {:layer 1,96} AtomicTidSplit({:linear_in "tid"} tid:Tid) returns({:linear "tid"} tid_left:Tid, {:linear "tid"} tid_right:Tid)
{ assert left#Tid(tid) && right#Tid(tid); tid_left := Tid(i#Tid(tid), true, false); tid_right := Tid(i#Tid(tid), false, true); }
procedure {:yields} {:layer 0} {:refines "AtomicTidSplit"} TidSplit({:linear_in "tid"} tid:Tid) returns({:linear "tid"} tid_left:Tid, {:linear "tid"} tid_right:Tid);

procedure {:both} {:layer 1,96} AtomicTidCombine({:linear_in "tid"} tid_left:Tid, {:linear_in "tid"} tid_right:Tid) returns({:linear "tid"} tid:Tid)
{ assert i#Tid(tid_left) == i#Tid(tid_right) && left#Tid(tid_left) && right#Tid(tid_right); tid := Tid(i#Tid(tid_left), true, true); }
procedure {:yields} {:layer 0} {:refines "AtomicTidCombine"} TidCombine({:linear_in "tid"} tid_left:Tid, {:linear_in "tid"} tid_right:Tid) returns({:linear "tid"} tid:Tid);

procedure {:both} {:layer 1,99} AtomicTidOutput({:linear_in "tid"} tid_in:Tid, {:linear_out "tid"} tid_out:Tid)
{ assert tid_in == tid_out; }
procedure {:yields} {:layer 0} {:refines "AtomicTidOutput"} TidOutput({:linear_in "tid"} tid_in:Tid, {:linear_out "tid"} tid_out:Tid);

procedure {:atomic} {:layer 1,95} AtomicPrimitiveReadField(x: int, f: fld) returns (y: int)
{ assert memAddr(x) && fieldAddr(f); y := mem[x][f]; }
procedure {:yields} {:layer 0} {:refines "AtomicPrimitiveReadField"} PrimitiveReadField(x: int, f: fld) returns (y: int);

procedure {:atomic} {:layer 1,95} AtomicPrimitiveWriteField(x: int, f: fld, y: int)
modifies mem;
{ assert memAddr(x) && fieldAddr(f); mem[x][f] := y; }
procedure {:yields} {:layer 0} {:refines "AtomicPrimitiveWriteField"} PrimitiveWriteField(x: int, f: fld, y: int);

procedure {:right} {:layer 1,99} AtomicPrimitiveFindFreePtrAbs() returns (o: obj)
modifies allocSet;
{ assume (memAddrAbs(o) && !allocSet[o] && o != nil); allocSet[o] := true; }
procedure {:yields} {:layer 0} {:refines "AtomicPrimitiveFindFreePtrAbs"} PrimitiveFindFreePtrAbs() returns (o: obj);

procedure{:atomic} {:layer 1,95} AtomicPrimitiveReadMarkStackPtr() returns (val: int)
{ val := MarkStackPtr; }
procedure{:yields} {:layer 0} {:refines "AtomicPrimitiveReadMarkStackPtr"} PrimitiveReadMarkStackPtr() returns (val: int);

procedure{:atomic} {:layer 1,95} AtomicPrimitiveSetMarkStackPtr(val: int)
modifies MarkStackPtr;
{ MarkStackPtr := val; }
procedure{:yields} {:layer 0} {:refines "AtomicPrimitiveSetMarkStackPtr"} PrimitiveSetMarkStackPtr(val: int);

procedure{:atomic} {:layer 1,95} AtomicPrimitiveReadMarkStack(ptr: int) returns (val: int)
{ val := MarkStack[ptr]; }
procedure{:yields} {:layer 0} {:refines "AtomicPrimitiveReadMarkStack"} PrimitiveReadMarkStack(ptr: int) returns (val: int);

procedure{:atomic} {:layer 1,95} AtomicPrimitiveWriteMarkStack(ptr: int, val: int)
modifies MarkStack;
{ MarkStack[ptr] := val; }
procedure{:yields} {:layer 0} {:refines "AtomicPrimitiveWriteMarkStack"} PrimitiveWriteMarkStack(ptr: int, val: int);

procedure {:atomic} {:layer 1,95} AtomicPrimitiveReadCollectorPhase() returns (phase: int)
{ phase := collectorPhase; }
procedure {:yields} {:layer 0} {:refines "AtomicPrimitiveReadCollectorPhase"} PrimitiveReadCollectorPhase() returns (phase: int);

procedure {:atomic} {:layer 1,95} AtomicPrimitiveSetCollectorPhase(phase:int)
modifies collectorPhase;
{ collectorPhase := phase; }
procedure {:yields} {:layer 0} {:refines "AtomicPrimitiveSetCollectorPhase"} PrimitiveSetCollectorPhase(phase:int);

procedure {:atomic} {:layer 1,95} AtomicPrimitiveReadMutatorPhase(i: int) returns (phase: int)
{ phase := mutatorPhase[i]; }
procedure {:yields} {:layer 0} {:refines "AtomicPrimitiveReadMutatorPhase"} PrimitiveReadMutatorPhase(i: int) returns (phase: int);

procedure {:atomic} {:layer 1,95} AtomicPrimitiveSetMutatorPhase(i: int, phase: int)
modifies mutatorPhase;
{ mutatorPhase[i] := phase; }
procedure {:yields} {:layer 0} {:refines "AtomicPrimitiveSetMutatorPhase"} PrimitiveSetMutatorPhase(i: int, phase: int);

procedure {:atomic} {:layer 1,95} AtomicPrimitiveReadSweepPtr() returns(val: int)
{ val := sweepPtr; }
procedure {:yields} {:layer 0} {:refines "AtomicPrimitiveReadSweepPtr"} PrimitiveReadSweepPtr() returns(val: int);

procedure {:atomic} {:layer 1,95} AtomicPrimitiveSetSweepPtr(val: int)
modifies sweepPtr;
{ sweepPtr := val; }
procedure {:yields} {:layer 0} {:refines "AtomicPrimitiveSetSweepPtr"} PrimitiveSetSweepPtr(val: int);

procedure {:atomic} {:layer 1,95} AtomicPrimitiveReadRootScanOn() returns(val: bool)
{ val := rootScanOn; }
procedure {:yields} {:layer 0} {:refines "AtomicPrimitiveReadRootScanOn"} PrimitiveReadRootScanOn() returns(val: bool);

procedure {:atomic} {:layer 1,95} AtomicPrimitiveSetRootScanOn(val: bool)
modifies rootScanOn;
{ rootScanOn := val; }
procedure {:yields} {:layer 0} {:refines "AtomicPrimitiveSetRootScanOn"} PrimitiveSetRootScanOn(val: bool);

procedure {:atomic} {:layer 1,95} AtomicPrimitiveReadRootScanBarrier() returns(val: int)
{ val := rootScanBarrier; }
procedure {:yields} {:layer 0} {:refines "AtomicPrimitiveReadRootScanBarrier"} PrimitiveReadRootScanBarrier() returns(val: int);

procedure {:atomic} {:layer 1,95} AtomicPrimitiveSetRootScanBarrier(val: int)
modifies rootScanBarrier;
{ rootScanBarrier := val; }
procedure {:yields} {:layer 0} {:refines "AtomicPrimitiveSetRootScanBarrier"} PrimitiveSetRootScanBarrier(val: int);

procedure {:atomic} {:layer 1,95} AtomicPrimitiveAddRootScanBarrier(val: int)
modifies rootScanBarrier;
{ rootScanBarrier := rootScanBarrier + val; }
procedure {:yields} {:layer 0} {:refines "AtomicPrimitiveAddRootScanBarrier"} PrimitiveAddRootScanBarrier(val: int);

procedure {:atomic} {:layer 1,95} AtomicPrimitiveMutatorsInRootScanBarrierAdd({:linear_in "tid"} tid_right: Tid)
modifies mutatorsInRootScanBarrier;
{ assert mutatorTidRight(tid_right); mutatorsInRootScanBarrier[i#Tid(tid_right)] := true; }
procedure {:yields} {:layer 0} {:refines "AtomicPrimitiveMutatorsInRootScanBarrierAdd"} PrimitiveMutatorsInRootScanBarrierAdd({:linear_in "tid"} tid_right: Tid);

procedure {:atomic} {:layer 1,95} AtomicPrimitiveMutatorsInRootScanBarrierRemove({:linear "tid"} tid_left: Tid) returns({:linear "tid"} tid_right: Tid)
modifies mutatorsInRootScanBarrier;
{ assert mutatorTidLeft(tid_left) && mutatorsInRootScanBarrier[i#Tid(tid_left)]; mutatorsInRootScanBarrier[i#Tid(tid_left)] := false; tid_right := Tid(i#Tid(tid_left), false, true); }
procedure {:yields} {:layer 0} {:refines "AtomicPrimitiveMutatorsInRootScanBarrierRemove"} PrimitiveMutatorsInRootScanBarrierRemove({:linear "tid"} tid_left: Tid) returns({:linear "tid"} tid_right: Tid);

procedure {:atomic} {:layer 1,95} AtomicPrimitiveWriteRoot(i: idx, val: int)
modifies root;
{ assert rootAddr(i); root[i] := val; }
procedure {:yields} {:layer 0} {:refines "AtomicPrimitiveWriteRoot"} PrimitiveWriteRoot(i: idx, val: int);

procedure {:atomic} {:layer 1,95} AtomicPrimitiveReadRoot(i: idx) returns (val: int)
{ assert rootAddr(i); val := root[i]; }
procedure {:yields} {:layer 0} {:refines "AtomicPrimitiveReadRoot"} PrimitiveReadRoot(i: idx) returns (val: int);

procedure {:atomic} {:layer 1,95} AtomicPrimitiveReadColor(i: int) returns (val: int)
{ assert memAddr(i); val := Color[i]; }
procedure {:yields} {:layer 0} {:refines "AtomicPrimitiveReadColor"} PrimitiveReadColor(i: int) returns (val: int);

procedure {:atomic} {:layer 1,95} AtomicPrimitiveSetColor(i: int, val: int)
modifies Color;
{ assert memAddr(i); Color[i] := val; }
procedure {:yields} {:layer 0} {:refines "AtomicPrimitiveSetColor"} PrimitiveSetColor(i: int, val: int);

procedure {:atomic} {:layer 1,95} AtomicPrimitiveLockCAS(next: int) returns (status: bool)
modifies lock;
{
  assert next != 0;
  if (*) {
    assume lock == 0; lock := next; status := true;
  } else {
    status := false;
  }
}
procedure {:yields} {:layer 0} {:refines "AtomicPrimitiveLockCAS"} PrimitiveLockCAS(next: int) returns (status: bool);

procedure {:atomic} {:layer 1,95} AtomicPrimitiveLockZero()
modifies lock;
{ lock := 0; }
procedure {:yields} {:layer 0} {:refines "AtomicPrimitiveLockZero"} PrimitiveLockZero();

procedure {:layer 99} {:inline 1} SetMemAbs1(x: idx, f: fld, y: idx)
modifies memAbs;
{
    memAbs[rootAbs[x]][f] := rootAbs[y];
}

procedure {:layer 99} {:inline 1} SetRootAbs1(x: idx, f: fld, y: idx)
modifies rootAbs;
{
    rootAbs[y] := memAbs[rootAbs[x]][f];
}

procedure {:layer 99} {:inline 1} SetMemAbs2(absPtr: obj)
modifies memAbs;
{
    memAbs[absPtr] := (lambda z: int :: if (fieldAddr(z)) then absPtr else memAbs[absPtr][z]);
}

procedure {:layer 99} {:inline 1} SetRootAbs2(y: idx, absPtr: obj)
modifies rootAbs;
{
    rootAbs[y] := absPtr;
}

procedure {:layer 95} {:inline 1} SetToAbs1()
modifies toAbs;
{
    toAbs := (lambda x: int :: if memAddr(x) && White(Color[x]) then nil else toAbs[x]);
}

procedure {:layer 95} {:inline 1} SetToAbs2(i: int, o: obj)
modifies toAbs;
{
    toAbs[i] := o;
}

procedure {:layer 95} {:inline 1} SetToAbs3()
modifies toAbs;
{
    toAbs := (lambda i:int :: if memAddr(i) then nil else Int(i));
}
