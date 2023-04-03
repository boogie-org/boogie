// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type {:linear "tid"} X;

const nil: X;
var {:layer 0,1} ghostLock: X;
var {:layer 0,1} lock: X;
var {:layer 0,1} currsize: int;
var {:layer 0,1} newsize: int;
var {:layer 0,1}{:linear "tid"} unallocated:[X]bool;

function {:inline} Inv(ghostLock: X, currsize: int, newsize: int) : (bool)
{
    0 <= currsize && currsize <= newsize &&
    (ghostLock == nil <==> currsize == newsize)
}

yield invariant {:layer 1} Yield();
invariant Inv(ghostLock, currsize, newsize);

yield invariant {:layer 1} YieldToReadCache({:linear "tid"} tid: X, old_currsize: int);
invariant tid != nil && old_currsize <= currsize;

yield invariant {:layer 1} YieldToWriteCache({:linear "tid"} tid: X, old_currsize: int, old_newsize: int);
invariant tid != nil && ghostLock == tid && old_currsize == currsize && old_newsize == newsize;

yield procedure {:layer 1} Allocate() returns ({:linear "tid"} xl: X)
ensures {:layer 1} xl != nil;
{
    call xl := AllocateLow();
}

yield procedure {:layer 1} main({:linear_in "tid"} xls: [X]bool)
requires {:layer 1} xls == MapConst(true);
{
    var {:linear "tid"} tid: X;

    call Init(xls);
    while (*)
    invariant {:yields} true;
    invariant call Yield();
    {
        par tid := Allocate() | Yield();
        async call Thread(tid);
    }
}

yield procedure {:layer 1} Thread({:linear "tid"} tid: X)
requires {:layer 1} tid != nil;
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

yield procedure {:layer 1} WriteCache({:linear "tid"} tid: X, index: int)
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

yield procedure {:layer 1} ReadCache({:linear "tid"} tid: X, start: int, bytesRead: int)
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

action {:layer 1} AtomicInit({:linear_in "tid"} xls:[X]bool)
modifies currsize, newsize, lock, ghostLock;
{ assert xls == MapConst(true); currsize := 0; newsize := 0; lock := nil; ghostLock := nil; }

yield procedure {:layer 0} Init({:linear_in "tid"} xls:[X]bool);
refines AtomicInit;

-> action {:layer 1} AtomicReadCurrsize({:linear "tid"} tid: X) returns (val: int)
{ assert tid != nil; assert lock == tid || ghostLock == tid; val := currsize; }

yield procedure {:layer 0} ReadCurrsize({:linear "tid"} tid: X) returns (val: int);
refines AtomicReadCurrsize;

-> action {:layer 1} AtomicReadNewsize({:linear "tid"} tid: X) returns (val: int)
{ assert tid != nil; assert lock == tid || ghostLock == tid; val := newsize; }

yield procedure {:layer 0} ReadNewsize({:linear "tid"} tid: X) returns (val: int);
refines AtomicReadNewsize;

action {:layer 1} AtomicWriteNewsize({:linear "tid"} tid: X, val: int)
modifies newsize, ghostLock;
{ assert tid != nil; assert lock == tid && ghostLock == nil; newsize := val; ghostLock := tid; }

yield procedure {:layer 0} WriteNewsize({:linear "tid"} tid: X, val: int);
refines AtomicWriteNewsize;

action {:layer 1} AtomicWriteCurrsize({:linear "tid"} tid: X, val: int)
modifies currsize, ghostLock;
{ assert tid != nil; assert lock == tid && ghostLock == tid; currsize := val; ghostLock := nil; }

yield procedure {:layer 0} WriteCurrsize({:linear "tid"} tid: X, val: int);
refines AtomicWriteCurrsize;

action {:layer 1} AtomicReadCacheEntry({:linear "tid"} tid: X, index: int)
{ assert 0 <= index && index < currsize; }

yield procedure {:layer 0} ReadCacheEntry({:linear "tid"} tid: X, index: int);
refines AtomicReadCacheEntry;

-> action {:layer 1} AtomicWriteCacheEntry({:linear "tid"} tid: X, index: int)
{ assert tid != nil; assert currsize <= index && ghostLock == tid; }

yield procedure {:layer 0} WriteCacheEntry({:linear "tid"} tid: X, index: int);
refines AtomicWriteCacheEntry;

-> action {:layer 1} atomic_acquire({:linear "tid"} tid: X)
modifies lock;
{ assert tid != nil; assume lock == nil; lock := tid; }

yield procedure {:layer 0} acquire({:linear "tid"} tid: X);
refines atomic_acquire;

<- action {:layer 1} atomic_release({:linear "tid"} tid: X)
modifies lock;
{ assert tid != nil; assert lock == tid; lock := nil; }

yield procedure {:layer 0} release({:linear "tid"} tid: X);
refines atomic_release;

action {:layer 1} AtomicAllocateLow() returns ({:linear "tid"} tid: X)
modifies unallocated;
{ assume tid != nil; assume unallocated[tid]; unallocated[tid] := false; }

yield procedure {:layer 0} AllocateLow() returns ({:linear "tid"} tid: X);
refines AtomicAllocateLow;
