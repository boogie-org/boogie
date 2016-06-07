// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
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

var {:layer 0} lock: int;
var {:layer 0} collectorPhase: int;
var {:layer 0} collectorPhaseDelayed: int;

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
procedure {:yields} {:layer 1} YieldLock()
requires {:expand} {:layer 1} LockInv(StoreBufferPresent, StoreBufferVal, Mem, lock, collectorPhase, collectorPhaseDelayed);
ensures {:layer 1} LockInv(StoreBufferPresent, StoreBufferVal, Mem, lock, collectorPhase, collectorPhaseDelayed);
{
    yield;
    assert {:layer 1} LockInv(StoreBufferPresent, StoreBufferVal, Mem, lock, collectorPhase, collectorPhaseDelayed);
}

procedure {:yields} {:layer 1} YieldStoreBufferLockAddrPresent({:linear "tid"} tid:int)
requires {:layer 1} StoreBufferPresent[tid][lockAddr];
ensures {:layer 1} StoreBufferPresent[tid][lockAddr];
{
    yield;
    assert {:layer 1} StoreBufferPresent[tid][lockAddr];
}

procedure {:yields} {:layer 1} YieldStoreBufferLockAddrAbsent({:linear "tid"} tid:int)
requires {:layer 1} !StoreBufferPresent[tid][lockAddr];
ensures {:layer 1} !StoreBufferPresent[tid][lockAddr];
{
    yield;
    assert {:layer 1} !StoreBufferPresent[tid][lockAddr];
}

procedure {:yields} {:layer 1} LockAcquire({:linear "tid"} tid: int)
requires {:layer 1} mutatorOrGcTid(tid);
requires {:layer 1} LockInv(StoreBufferPresent, StoreBufferVal, Mem, lock, collectorPhase, collectorPhaseDelayed);
ensures {:layer 1} LockInv(StoreBufferPresent, StoreBufferVal, Mem, lock, collectorPhase, collectorPhaseDelayed);
ensures {:right} |{ A: assert mutatorOrGcTid(tid); assume lock == 0; lock := tid; return true; }|;
{
    var status:bool;
    call YieldLock();
    while (true)
    invariant {:layer 1} LockInv(StoreBufferPresent, StoreBufferVal, Mem, lock, collectorPhase, collectorPhaseDelayed);
    {
        call status := LockCAS(tid);
        if (status)
        {
    	    call YieldLock();
            return;
        }
	call YieldLock();
    }
    call YieldLock();
}

procedure {:yields} {:layer 1} LockRelease({:linear "tid"} tid:int)
requires {:layer 1} mutatorOrGcTid(tid);
requires {:layer 1} !StoreBufferPresent[tid][lockAddr];
requires {:layer 1} LockInv(StoreBufferPresent, StoreBufferVal, Mem, lock, collectorPhase, collectorPhaseDelayed);
ensures {:layer 1} !StoreBufferPresent[tid][lockAddr];
ensures {:layer 1} LockInv(StoreBufferPresent, StoreBufferVal, Mem, lock, collectorPhase, collectorPhaseDelayed);
ensures {:atomic} |{ A: assert mutatorOrGcTid(tid); assert lock == tid; lock := 0; return true; }|;
{
    par YieldLock() | YieldStoreBufferLockAddrAbsent(tid);
    call LockZero(tid);
    par YieldLock() | YieldStoreBufferLockAddrPresent(tid);
    call FlushStoreBufferEntryForLock(tid);
    par YieldLock() | YieldStoreBufferLockAddrAbsent(tid);
}

procedure {:yields} {:layer 1} ReadCollectorPhaseLocked({:linear "tid"} tid: int) returns (phase: int)
requires {:layer 1} mutatorOrGcTid(tid);
requires {:layer 1} LockInv(StoreBufferPresent, StoreBufferVal, Mem, lock, collectorPhase, collectorPhaseDelayed);
ensures {:layer 1} LockInv(StoreBufferPresent, StoreBufferVal, Mem, lock, collectorPhase, collectorPhaseDelayed);
ensures {:atomic} |{ A: assert mutatorOrGcTid(tid); assert lock == tid; phase := collectorPhase; return true; }|;
{
    call YieldLock();
    call phase := PrimitiveRead(tid, collectorPhaseAddr);
    call YieldLock();    
}

procedure {:yields} {:layer 1} ReadCollectorPhaseUnlocked({:linear "tid"} tid: int) returns (phase: int)
requires {:layer 1} mutatorOrGcTid(tid);
requires {:layer 1} LockInv(StoreBufferPresent, StoreBufferVal, Mem, lock, collectorPhase, collectorPhaseDelayed);
ensures {:layer 1} LockInv(StoreBufferPresent, StoreBufferVal, Mem, lock, collectorPhase, collectorPhaseDelayed);
ensures {:atomic} |{ A: assert mutatorOrGcTid(tid); assert lock != tid; phase := collectorPhaseDelayed; return true; }|;
{
    call YieldLock();
    call phase := PrimitiveRead(tid, collectorPhaseAddr);
    call YieldLock();    
}

procedure {:yields} {:layer 1} SetCollectorPhase({:linear "tid"} tid: int, phase: int)
requires {:layer 1} mutatorOrGcTid(tid);
requires {:layer 1} LockInv(StoreBufferPresent, StoreBufferVal, Mem, lock, collectorPhase, collectorPhaseDelayed);
ensures {:layer 1} LockInv(StoreBufferPresent, StoreBufferVal, Mem, lock, collectorPhase, collectorPhaseDelayed);
ensures {:atomic} |{ A: assert mutatorOrGcTid(tid); assert lock == tid; assert collectorPhase == collectorPhaseDelayed; collectorPhase := phase; return true; }|;
{
    call YieldLock();
    call PrimitiveSetCollectorPhase(tid, phase);
    call YieldLock();
}

procedure {:yields} {:layer 1} SyncCollectorPhase({:linear "tid"} tid: int)
requires {:layer 1} LockInv(StoreBufferPresent, StoreBufferVal, Mem, lock, collectorPhase, collectorPhaseDelayed);
ensures {:layer 1} LockInv(StoreBufferPresent, StoreBufferVal, Mem, lock, collectorPhase, collectorPhaseDelayed);
ensures {:atomic} |{ A: collectorPhaseDelayed := collectorPhase; return true; }|;
{
    call YieldLock();
    call FlushStoreBufferEntryForCollectorPhase();
    call YieldLock();
}

procedure {:yields} {:layer 1} Barrier({:linear "tid"} tid: int)
requires {:layer 1} mutatorOrGcTid(tid);
requires {:layer 1} LockInv(StoreBufferPresent, StoreBufferVal, Mem, lock, collectorPhase, collectorPhaseDelayed);
ensures {:layer 1} LockInv(StoreBufferPresent, StoreBufferVal, Mem, lock, collectorPhase, collectorPhaseDelayed);
ensures {:atomic} |{ A: assert mutatorOrGcTid(tid); assert lock == tid; assume collectorPhase == collectorPhaseDelayed; return true; }|;
{
   call YieldLock();
   call WaitForFlush(tid);
   call YieldLock();
}

// Layer 0
procedure {:yields} {:layer 0,1} LockCAS(tid: int) returns (status: bool);
ensures {:atomic} |{ A: goto B, C; 
                     B: assume Mem[lockAddr] == 0; Mem[lockAddr] := 1; lock := tid; status := true; return true; 
                     C: status := false; return true; 
                  }|;

procedure {:yields} {:layer 0,1} LockZero(tid: int);
ensures {:atomic} |{ A: assert !StoreBufferPresent[tid][lockAddr]; StoreBufferPresent[tid][lockAddr] := true; StoreBufferVal[tid][lockAddr] := 0; return true; }|;

procedure {:yields} {:layer 0,1} FlushStoreBufferEntryForLock(tid: int);
ensures {:atomic} |{ A: assert StoreBufferPresent[tid][lockAddr]; assume StoreBufferPresent[tid] == MapConstBool(false)[lockAddr := true]; Mem[lockAddr] := StoreBufferVal[tid][lockAddr]; StoreBufferPresent[tid][lockAddr] := false; lock := 0; return true; }|;

procedure {:yields} {:layer 0,1} PrimitiveRead(tid: int, addr: int) returns (val: int);
ensures {:atomic} |{ A: goto B, C;
                     B: assume StoreBufferPresent[tid][addr]; val := StoreBufferVal[tid][addr]; return true; 
                     C: assume !StoreBufferPresent[tid][addr]; val := Mem[addr]; return true; }|;

procedure {:yields} {:layer 0,1} PrimitiveSetCollectorPhase(tid: int, phase:int);
ensures {:atomic} |{ A: StoreBufferPresent[tid][collectorPhaseAddr] := true; StoreBufferVal[tid][collectorPhaseAddr] := phase; collectorPhase := phase; return true; }|;

procedure {:yields} {:layer 0,1} FlushStoreBufferEntryForCollectorPhase();
ensures {:atomic} |{ var tid:int; A: assume mutatorOrGcTid(tid) && StoreBufferPresent[tid][collectorPhaseAddr]; Mem[collectorPhaseAddr] := StoreBufferVal[tid][collectorPhaseAddr]; StoreBufferPresent[tid][collectorPhaseAddr] := false; collectorPhaseDelayed := Mem[collectorPhaseAddr]; return true; }|;

procedure {:yields} {:layer 0,1} WaitForFlush(tid: int);
ensures {:atomic} |{ A: assume StoreBufferPresent[tid] == MapConstBool(false); return true; }|;
