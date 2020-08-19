// RUN: %boogie -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function {:builtin "MapConst"} MapConstBool(bool) : [int]bool;

function {:inline} {:linear "tid"} TidCollector(x: int) : [int]bool
{
  MapConstBool(false)[x := true]
}

function {:inline} {:linear "addr"} AddrCollector(x: int) : [int]bool
{
  MapConstBool(false)[x := true]
}

const numMutators: int;
axiom 0 < numMutators;
function {:inline} mutatorTid(i: int) : bool { 1 <= i && i <= numMutators }

const GcTid: int;
axiom numMutators < GcTid;
function {:inline} mutatorOrGcTid(i: int) : bool { (1 <= i && i <= numMutators) || i == GcTid }

const lockAddr: int;
axiom 0 < lockAddr;
const collectorPhaseAddr: int;
axiom lockAddr < collectorPhaseAddr;

var {:layer 0,1} Mem: [int]int;
var {:layer 0,1} StoreBufferVal: [int][int]int;
var {:layer 0,1} StoreBufferPresent: [int][int]bool;

var {:layer 0,2} lock: int;
var {:layer 0,2} collectorPhase: int;
var {:layer 0,2} collectorPhaseDelayed: int;

function {:inline} LockInv(StoreBufferPresent:[int][int]bool, StoreBufferVal:[int][int]int, Mem:[int]int, lock:int, collectorPhase:int, collectorPhaseDelayed:int): bool
{
  (Mem[lockAddr] == 0 <==> lock == 0) &&
  (forall i:int :: mutatorOrGcTid(i) && StoreBufferPresent[i][lockAddr] ==> StoreBufferVal[i][lockAddr] == 0) &&
  (forall i:int :: mutatorOrGcTid(i) ==> lock == i || StoreBufferPresent[i] == MapConstBool(false)) &&
  (Mem[collectorPhaseAddr] == collectorPhase || (exists i:int :: mutatorOrGcTid(i) && StoreBufferPresent[i][collectorPhaseAddr])) &&
  (forall i:int :: mutatorOrGcTid(i) && StoreBufferPresent[i][collectorPhaseAddr] ==> StoreBufferVal[i][collectorPhaseAddr] == collectorPhase) &&
  collectorPhaseDelayed == Mem[collectorPhaseAddr]
}

// Layer 1
procedure {:yield_invariant} {:layer 1} YieldLock();
requires {:expand} LockInv(StoreBufferPresent, StoreBufferVal, Mem, lock, collectorPhase, collectorPhaseDelayed);

procedure {:yield_invariant} {:layer 1} YieldStoreBufferLockAddrPresent({:linear "tid"} tid:int);
requires StoreBufferPresent[tid][lockAddr];

procedure {:yield_invariant} {:layer 1} YieldStoreBufferLockAddrAbsent({:linear "tid"} tid:int);
requires !StoreBufferPresent[tid][lockAddr];

procedure {:right} {:layer 2} AtomicLockAcquire({:linear "tid"} tid: int)
modifies lock;
{ assert mutatorOrGcTid(tid); assume lock == 0; lock := tid; }

procedure {:yields} {:layer 1} {:refines "AtomicLockAcquire"}
{:yield_preserves "YieldLock"}
LockAcquire({:linear "tid"} tid: int)
requires {:layer 1} mutatorOrGcTid(tid);
{
    var status:bool;
    while (true)
    invariant {:yields} {:layer 1} {:yield_loop "YieldLock"} true;
    {
        call status := LockCAS(tid);
        if (status)
        {
            return;
        }
    }
}

procedure {:atomic} {:layer 2} AtomicLockRelease({:linear "tid"} tid:int)
modifies lock;
{ assert mutatorOrGcTid(tid); assert lock == tid; lock := 0; }

procedure {:yields} {:layer 1} {:refines "AtomicLockRelease"}
{:yield_preserves "YieldLock"}
{:yield_preserves "YieldStoreBufferLockAddrAbsent", tid}
LockRelease({:linear "tid"} tid:int)
requires {:layer 1} mutatorOrGcTid(tid);
{
    call LockZero(tid);
    par YieldLock() | YieldStoreBufferLockAddrPresent(tid);
    call FlushStoreBufferEntryForLock(tid);
}

procedure {:atomic} {:layer 2} AtomicReadCollectorPhaseLocked({:linear "tid"} tid: int) returns (phase: int)
{ assert mutatorOrGcTid(tid); assert lock == tid; phase := collectorPhase; }

procedure {:yields} {:layer 1} {:refines "AtomicReadCollectorPhaseLocked"}
{:yield_preserves "YieldLock"}
ReadCollectorPhaseLocked({:linear "tid"} tid: int) returns (phase: int)
requires {:layer 1} mutatorOrGcTid(tid);
{
    call phase := PrimitiveRead(tid, collectorPhaseAddr);
}

procedure {:atomic} {:layer 2} AtomicReadCollectorPhaseUnlocked({:linear "tid"} tid: int) returns (phase: int)
{ assert mutatorOrGcTid(tid); assert lock != tid; phase := collectorPhaseDelayed; }

procedure {:yields} {:layer 1} {:refines "AtomicReadCollectorPhaseUnlocked"}
{:yield_preserves "YieldLock"}
ReadCollectorPhaseUnlocked({:linear "tid"} tid: int) returns (phase: int)
requires {:layer 1} mutatorOrGcTid(tid);
{
    call phase := PrimitiveRead(tid, collectorPhaseAddr);
}

procedure {:atomic} {:layer 2} AtomicSetCollectorPhase({:linear "tid"} tid: int, phase: int)
modifies collectorPhase;
{ assert mutatorOrGcTid(tid); assert lock == tid; assert collectorPhase == collectorPhaseDelayed; collectorPhase := phase; }

procedure {:yields} {:layer 1} {:refines "AtomicSetCollectorPhase"}
{:yield_preserves "YieldLock"}
SetCollectorPhase({:linear "tid"} tid: int, phase: int)
requires {:layer 1} mutatorOrGcTid(tid);
{
    call PrimitiveSetCollectorPhase(tid, phase);
}

procedure {:atomic} {:layer 2} AtomicSyncCollectorPhase({:linear "tid"} tid: int)
modifies collectorPhaseDelayed;
{ collectorPhaseDelayed := collectorPhase; }

procedure {:yields} {:layer 1} {:refines "AtomicSyncCollectorPhase"}
{:yield_preserves "YieldLock"}
SyncCollectorPhase({:linear "tid"} tid: int)
{
    call FlushStoreBufferEntryForCollectorPhase();
}

procedure {:atomic} {:layer 2} AtomicBarrier({:linear "tid"} tid: int)
{ assert mutatorOrGcTid(tid); assert lock == tid; assume collectorPhase == collectorPhaseDelayed; }

procedure {:yields} {:layer 1} {:refines "AtomicBarrier"}
{:yield_preserves "YieldLock"}
Barrier({:linear "tid"} tid: int)
requires {:layer 1} mutatorOrGcTid(tid);
{
   call WaitForFlush(tid);
}

// Layer 0
procedure {:atomic} {:layer 1} AtomicLockCAS(tid: int) returns (status: bool)
modifies Mem, lock;
{
  if (*) {
    assume Mem[lockAddr] == 0;
    Mem[lockAddr] := 1;
    lock := tid;
    status := true;
  } else {
    status := false;
  }
}

procedure {:yields} {:layer 0} {:refines "AtomicLockCAS"} LockCAS(tid: int) returns (status: bool);

procedure {:atomic} {:layer 1} AtomicLockZero(tid: int)
modifies StoreBufferPresent, StoreBufferVal;
{ assert !StoreBufferPresent[tid][lockAddr]; StoreBufferPresent[tid][lockAddr] := true; StoreBufferVal[tid][lockAddr] := 0; }

procedure {:yields} {:layer 0} {:refines "AtomicLockZero"} LockZero(tid: int);

procedure {:atomic} {:layer 1} AtomicFlushStoreBufferEntryForLock(tid: int)
modifies Mem, StoreBufferPresent, lock;
{
  assert StoreBufferPresent[tid][lockAddr];
  assume StoreBufferPresent[tid] == MapConstBool(false)[lockAddr := true];
  Mem[lockAddr] := StoreBufferVal[tid][lockAddr];
  StoreBufferPresent[tid][lockAddr] := false;
  lock := 0;
}

procedure {:yields} {:layer 0} {:refines "AtomicFlushStoreBufferEntryForLock"} FlushStoreBufferEntryForLock(tid: int);

procedure {:atomic} {:layer 1} AtomicPrimitiveRead(tid: int, addr: int) returns (val: int)
{
  if (StoreBufferPresent[tid][addr]) {
    val := StoreBufferVal[tid][addr];
  } else {
    val := Mem[addr];
  }
}

procedure {:yields} {:layer 0} {:refines "AtomicPrimitiveRead"} PrimitiveRead(tid: int, addr: int) returns (val: int);

procedure {:atomic} {:layer 1} AtomicPrimitiveSetCollectorPhase(tid: int, phase:int)
modifies StoreBufferPresent, StoreBufferVal, collectorPhase;
{ StoreBufferPresent[tid][collectorPhaseAddr] := true; StoreBufferVal[tid][collectorPhaseAddr] := phase; collectorPhase := phase; }

procedure {:yields} {:layer 0} {:refines "AtomicPrimitiveSetCollectorPhase"} PrimitiveSetCollectorPhase(tid: int, phase:int);

procedure {:atomic} {:layer 1} AtomicFlushStoreBufferEntryForCollectorPhase()
modifies Mem, StoreBufferPresent, collectorPhaseDelayed;
{
  var tid:int;
  assume mutatorOrGcTid(tid) && StoreBufferPresent[tid][collectorPhaseAddr];
  Mem[collectorPhaseAddr] := StoreBufferVal[tid][collectorPhaseAddr];
  StoreBufferPresent[tid][collectorPhaseAddr] := false;
  collectorPhaseDelayed := Mem[collectorPhaseAddr];
}

procedure {:yields} {:layer 0} {:refines "AtomicFlushStoreBufferEntryForCollectorPhase"} FlushStoreBufferEntryForCollectorPhase();

procedure {:atomic} {:layer 1} AtomicWaitForFlush(tid: int)
{ assume StoreBufferPresent[tid] == MapConstBool(false); }

procedure {:yields} {:layer 0} {:refines "AtomicWaitForFlush"} WaitForFlush(tid: int);
