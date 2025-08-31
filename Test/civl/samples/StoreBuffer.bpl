// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type X = int;

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
  (forall i:int :: mutatorOrGcTid(i) ==> lock == i || StoreBufferPresent[i] == MapConst(false)) &&
  (Mem[collectorPhaseAddr] == collectorPhase || (exists i:int :: mutatorOrGcTid(i) && StoreBufferPresent[i][collectorPhaseAddr])) &&
  (forall i:int :: mutatorOrGcTid(i) && StoreBufferPresent[i][collectorPhaseAddr] ==> StoreBufferVal[i][collectorPhaseAddr] == collectorPhase) &&
  collectorPhaseDelayed == Mem[collectorPhaseAddr]
}

// Layer 1
yield invariant {:layer 1} YieldLock();
preserves {:expand} LockInv(StoreBufferPresent, StoreBufferVal, Mem, lock, collectorPhase, collectorPhaseDelayed);

yield invariant {:layer 1} YieldStoreBufferLockAddrPresent({:linear} tid: One int);
preserves StoreBufferPresent[tid->val][lockAddr];

yield invariant {:layer 1} YieldStoreBufferLockAddrAbsent({:linear} tid: One int);
preserves !StoreBufferPresent[tid->val][lockAddr];

right action {:layer 2} AtomicLockAcquire({:linear} tid: One int)
modifies lock;
{ assert mutatorOrGcTid(tid->val); assume lock == 0; lock := tid->val; }

yield procedure {:layer 1} LockAcquire({:linear} tid: One int)
refines AtomicLockAcquire;
preserves call YieldLock();
requires {:layer 1} mutatorOrGcTid(tid->val);
{
    var status:bool;
    while (true)
    invariant {:yields} true;
    invariant call YieldLock();
    {
        call status := LockCAS(tid->val);
        if (status)
        {
            return;
        }
    }
}

atomic action {:layer 2} AtomicLockRelease({:linear} tid: One int)
modifies lock;
{ assert mutatorOrGcTid(tid->val); assert lock == tid->val; lock := 0; }

yield procedure {:layer 1} LockRelease({:linear} tid: One int)
refines AtomicLockRelease;
requires {:layer 1} mutatorOrGcTid(tid->val);
preserves call YieldLock();
preserves call YieldStoreBufferLockAddrAbsent(tid);
{
    call LockZero(tid->val);
    call YieldLock() | YieldStoreBufferLockAddrPresent(tid);
    call FlushStoreBufferEntryForLock(tid->val);
}

atomic action {:layer 2} AtomicReadCollectorPhaseLocked({:linear} tid: One int) returns (phase: int)
{ assert mutatorOrGcTid(tid->val); assert lock == tid->val; phase := collectorPhase; }

yield procedure {:layer 1} ReadCollectorPhaseLocked({:linear} tid: One int) returns (phase: int)
refines AtomicReadCollectorPhaseLocked;
requires {:layer 1} mutatorOrGcTid(tid->val);
preserves call YieldLock();
{
    call phase := PrimitiveRead(tid->val, collectorPhaseAddr);
}

atomic action {:layer 2} AtomicReadCollectorPhaseUnlocked({:linear} tid: One int) returns (phase: int)
{ assert mutatorOrGcTid(tid->val); assert lock != tid->val; phase := collectorPhaseDelayed; }

yield procedure {:layer 1} ReadCollectorPhaseUnlocked({:linear} tid: One int) returns (phase: int)
refines AtomicReadCollectorPhaseUnlocked;
requires {:layer 1} mutatorOrGcTid(tid->val);
preserves call YieldLock();
{
    call phase := PrimitiveRead(tid->val, collectorPhaseAddr);
}

atomic action {:layer 2} AtomicSetCollectorPhase({:linear} tid: One int, phase: int)
modifies collectorPhase;
{ assert mutatorOrGcTid(tid->val); assert lock == tid->val; assert collectorPhase == collectorPhaseDelayed; collectorPhase := phase; }

yield procedure {:layer 1}
SetCollectorPhase({:linear} tid: One int, phase: int)
refines AtomicSetCollectorPhase;
requires {:layer 1} mutatorOrGcTid(tid->val);
preserves call YieldLock();
{
    call PrimitiveSetCollectorPhase(tid->val, phase);
}

atomic action {:layer 2} AtomicSyncCollectorPhase({:linear} tid: One int)
modifies collectorPhaseDelayed;
{ collectorPhaseDelayed := collectorPhase; }

yield procedure {:layer 1} SyncCollectorPhase({:linear} tid: One int)
refines AtomicSyncCollectorPhase;
preserves call YieldLock();
{
    call FlushStoreBufferEntryForCollectorPhase();
}

atomic action {:layer 2} AtomicBarrier({:linear} tid: One int)
{ assert mutatorOrGcTid(tid->val); assert lock == tid->val; assume collectorPhase == collectorPhaseDelayed; }

yield procedure {:layer 1} Barrier({:linear} tid: One int)
refines AtomicBarrier;
requires {:layer 1} mutatorOrGcTid(tid->val);
preserves call YieldLock();
{
   call WaitForFlush(tid->val);
}

// Layer 0
atomic action {:layer 1} AtomicLockCAS(tid: int) returns (status: bool)
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

yield procedure {:layer 0} LockCAS(tid: int) returns (status: bool);
refines AtomicLockCAS;

atomic action {:layer 1} AtomicLockZero(tid: int)
modifies StoreBufferPresent, StoreBufferVal;
{ assert !StoreBufferPresent[tid][lockAddr]; StoreBufferPresent[tid][lockAddr] := true; StoreBufferVal[tid][lockAddr] := 0; }

yield procedure {:layer 0} LockZero(tid: int);
refines AtomicLockZero;

atomic action {:layer 1} AtomicFlushStoreBufferEntryForLock(tid: int)
modifies Mem, StoreBufferPresent, lock;
{
  assert StoreBufferPresent[tid][lockAddr];
  assume StoreBufferPresent[tid] == MapConst(false)[lockAddr := true];
  Mem[lockAddr] := StoreBufferVal[tid][lockAddr];
  StoreBufferPresent[tid][lockAddr] := false;
  lock := 0;
}

yield procedure {:layer 0} FlushStoreBufferEntryForLock(tid: int);
refines AtomicFlushStoreBufferEntryForLock;

atomic action {:layer 1} AtomicPrimitiveRead(tid: int, addr: int) returns (val: int)
{
  if (StoreBufferPresent[tid][addr]) {
    val := StoreBufferVal[tid][addr];
  } else {
    val := Mem[addr];
  }
}

yield procedure {:layer 0} PrimitiveRead(tid: int, addr: int) returns (val: int);
refines AtomicPrimitiveRead;

atomic action {:layer 1} AtomicPrimitiveSetCollectorPhase(tid: int, phase:int)
modifies StoreBufferPresent, StoreBufferVal, collectorPhase;
{ StoreBufferPresent[tid][collectorPhaseAddr] := true; StoreBufferVal[tid][collectorPhaseAddr] := phase; collectorPhase := phase; }

yield procedure {:layer 0} PrimitiveSetCollectorPhase(tid: int, phase:int);
refines AtomicPrimitiveSetCollectorPhase;

atomic action {:layer 1} AtomicFlushStoreBufferEntryForCollectorPhase()
modifies Mem, StoreBufferPresent, collectorPhaseDelayed;
{
  var tid:int;
  assume mutatorOrGcTid(tid) && StoreBufferPresent[tid][collectorPhaseAddr];
  Mem[collectorPhaseAddr] := StoreBufferVal[tid][collectorPhaseAddr];
  StoreBufferPresent[tid][collectorPhaseAddr] := false;
  collectorPhaseDelayed := Mem[collectorPhaseAddr];
}

yield procedure {:layer 0} FlushStoreBufferEntryForCollectorPhase();
refines AtomicFlushStoreBufferEntryForCollectorPhase;

atomic action {:layer 1} AtomicWaitForFlush(tid: int)
{ assume StoreBufferPresent[tid] == MapConst(false); }

yield procedure {:layer 0} WaitForFlush(tid: int);
refines AtomicWaitForFlush;
