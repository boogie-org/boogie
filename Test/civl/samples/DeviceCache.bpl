// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type X;

const nil: X;
var {:layer 0,1} ghostLock: X;
var {:layer 0,1} lock: X;
var {:layer 0,1} currsize: int;
var {:layer 0,1} newsize: int;
var {:layer 0,1}{:linear} unallocated: Set X;

function {:inline} Inv(ghostLock: X, currsize: int, newsize: int) : (bool)
{
    0 <= currsize && currsize <= newsize &&
    (ghostLock == nil <==> currsize == newsize)
}

yield invariant {:layer 1} Yield();
preserves Inv(ghostLock, currsize, newsize);

yield invariant {:layer 1} YieldToReadCache({:linear} tid: One X, old_currsize: int);
preserves tid->val != nil && old_currsize <= currsize;

yield invariant {:layer 1} YieldToWriteCache({:linear} tid: One X, old_currsize: int, old_newsize: int);
preserves tid->val != nil && ghostLock == tid->val && old_currsize == currsize && old_newsize == newsize;

yield procedure {:layer 1} Allocate() returns ({:linear} xl: One X)
ensures {:layer 1} xl->val != nil;
{
    call xl := AllocateLow();
}

yield procedure {:layer 1} main({:linear_in} xls: Set X)
requires {:layer 1} xls->val == MapConst(true);
{
    var {:linear} tid: One X;

    call Init(xls);
    while (*)
    invariant {:yields} true;
    invariant call Yield();
    {
        call tid := Allocate() | Yield();
        async call Thread(tid);
    }
}

yield procedure {:layer 1} Thread({:linear} tid: One X)
requires {:layer 1} tid->val != nil;
preserves call Yield();
{
    var start, size: int;
    var bytesRead, i, tmp: int;

    havoc start, size;
    assume (0 <= start && 0 <= size);

    bytesRead := size;
    call acquire(tid);
    call i := ReadCurrsize(tid);
    call tmp := ReadNewsize(tid);
    if (start + size <= i) {
        call release(tid);
        goto COPY_TO_BUFFER;
    } else if (tmp > i) {
        bytesRead := if (start <= i) then (i - start) else 0;
        call release(tid);
        goto COPY_TO_BUFFER;
    } else {
        call WriteNewsize(tid, start + size);
        call release(tid);
        goto READ_DEVICE;
    }

READ_DEVICE:
    call WriteCache(tid, start + size);
    call acquire(tid);
    call tmp := ReadNewsize(tid);
    call WriteCurrsize(tid, tmp);
    call release(tid);

COPY_TO_BUFFER:
    if (0 < bytesRead)
    {
        call ReadCache(tid, start, bytesRead);
    }
}

yield procedure {:layer 1} WriteCache({:linear} tid: One X, index: int)
preserves call Yield();
preserves call YieldToWriteCache(tid, old(currsize), old(newsize));
{
    var j: int;

    call j := ReadCurrsize(tid);
    while (j < index)
    invariant {:yields} true;
    invariant call Yield();
    invariant call YieldToWriteCache(tid, old(currsize), old(newsize));
    invariant {:layer 1} old(currsize) <= j;
    {
        call WriteCacheEntry(tid, j);
        j := j + 1;
    }
}

yield procedure {:layer 1} ReadCache({:linear} tid: One X, start: int, bytesRead: int)
requires {:layer 1} 0 <= start && 0 < bytesRead;
preserves call Yield();
requires call YieldToReadCache(tid, start + bytesRead);
preserves call YieldToReadCache(tid, old(currsize));

{
    var j: int;

    j := 0;
    while(j < bytesRead)
    invariant {:yields} true;
    invariant call Yield();
    invariant call YieldToReadCache(tid, old(currsize));
    invariant {:layer 1} 0 <= j && j <= bytesRead;
    {
        call ReadCacheEntry(tid, start + j);
        j := j + 1;
    }
}

atomic action {:layer 1} AtomicInit({:linear_in} xls: Set X)
modifies currsize, newsize, lock, ghostLock;
{ assert xls->val == MapConst(true); currsize := 0; newsize := 0; lock := nil; ghostLock := nil; }

yield procedure {:layer 0} Init({:linear_in} xls: Set X);
refines AtomicInit;

right action {:layer 1} AtomicReadCurrsize({:linear} tid: One X) returns (val: int)
{ assert tid->val != nil; assert lock == tid->val || ghostLock == tid->val; val := currsize; }

yield procedure {:layer 0} ReadCurrsize({:linear} tid: One X) returns (val: int);
refines AtomicReadCurrsize;

right action {:layer 1} AtomicReadNewsize({:linear} tid: One X) returns (val: int)
{ assert tid->val != nil; assert lock == tid->val || ghostLock == tid->val; val := newsize; }

yield procedure {:layer 0} ReadNewsize({:linear} tid: One X) returns (val: int);
refines AtomicReadNewsize;

atomic action {:layer 1} AtomicWriteNewsize({:linear} tid: One X, val: int)
modifies newsize, ghostLock;
{ assert tid->val != nil; assert lock == tid->val && ghostLock == nil; newsize := val; ghostLock := tid->val; }

yield procedure {:layer 0} WriteNewsize({:linear} tid: One X, val: int);
refines AtomicWriteNewsize;

atomic action {:layer 1} AtomicWriteCurrsize({:linear} tid: One X, val: int)
modifies currsize, ghostLock;
{ assert tid->val != nil; assert lock == tid->val && ghostLock == tid->val; currsize := val; ghostLock := nil; }

yield procedure {:layer 0} WriteCurrsize({:linear} tid: One X, val: int);
refines AtomicWriteCurrsize;

atomic action {:layer 1} AtomicReadCacheEntry({:linear} tid: One X, index: int)
{ assert 0 <= index && index < currsize; }

yield procedure {:layer 0} ReadCacheEntry({:linear} tid: One X, index: int);
refines AtomicReadCacheEntry;

right action {:layer 1} AtomicWriteCacheEntry({:linear} tid: One X, index: int)
{ assert tid->val != nil; assert currsize <= index && ghostLock == tid->val; }

yield procedure {:layer 0} WriteCacheEntry({:linear} tid: One X, index: int);
refines AtomicWriteCacheEntry;

right action {:layer 1} atomic_acquire({:linear} tid: One X)
modifies lock;
{ assert tid->val != nil; assume lock == nil; lock := tid->val; }

yield procedure {:layer 0} acquire({:linear} tid: One X);
refines atomic_acquire;

left action {:layer 1} atomic_release({:linear} tid: One X)
modifies lock;
{ assert tid->val != nil; assert lock == tid->val; lock := nil; }

yield procedure {:layer 0} release({:linear} tid: One X);
refines atomic_release;

atomic action {:layer 1} AtomicAllocateLow() returns ({:linear} tid: One X)
modifies unallocated;
{ assume tid->val != nil; assume Set_Contains(unallocated, tid->val); call One_Split(unallocated, tid); }

yield procedure {:layer 0} AllocateLow() returns ({:linear} tid: One X);
refines AtomicAllocateLow;
