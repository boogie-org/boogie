// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type X;
function {:builtin "MapConst"} mapconstbool(bool): [X]bool;
const nil: X;
var {:layer 0,1} ghostLock: X;
var {:layer 0,1} lock: X;
var {:layer 0,1} currsize: int;
var {:layer 0,1} newsize: int;
var {:layer 0,1}{:linear "tid"} unallocated:[X]bool;

function {:builtin "MapConst"} MapConstBool(bool) : [X]bool;
function {:inline} {:linear "tid"} TidCollector(x: X) : [X]bool
{
  MapConstBool(false)[x := true]
}
function {:inline} {:linear "tid"} TidSetCollector(x: [X]bool) : [X]bool
{
  x
}

function {:inline} Inv(ghostLock: X, currsize: int, newsize: int) : (bool)
{
    0 <= currsize && currsize <= newsize &&
    (ghostLock == nil <==> currsize == newsize)
}

procedure {:yields} {:layer 1} Yield()
requires {:layer 1} Inv(ghostLock, currsize, newsize);
ensures {:layer 1} Inv(ghostLock, currsize, newsize);
{
   yield;
   assert {:layer 1} Inv(ghostLock, currsize, newsize);
}

procedure {:yields} {:layer 1} YieldToReadCache({:linear "tid"} tid: X)
requires {:layer 1} Inv(ghostLock, currsize, newsize) && tid != nil;
ensures {:layer 1} Inv(ghostLock, currsize, newsize) && old(currsize) <= currsize;
{
   yield;
   assert {:layer 1} Inv(ghostLock, currsize, newsize) && old(currsize) <= currsize;
}

procedure {:yields} {:layer 1} YieldToWriteCache({:linear "tid"} tid: X)
requires {:layer 1} Inv(ghostLock, currsize, newsize) && ghostLock == tid && tid != nil;
ensures {:layer 1} Inv(ghostLock, currsize, newsize) && ghostLock == tid && old(currsize) == currsize && old(newsize) == newsize;
{
    yield;
    assert {:layer 1} Inv(ghostLock, currsize, newsize) && tid != nil && ghostLock == tid && old(currsize) == currsize && old(newsize) == newsize;
}

procedure {:yields} {:layer 1} Allocate() returns ({:linear "tid"} xl: X)
ensures {:layer 1} xl != nil;
{
    yield;
    call xl := AllocateLow();
    yield;
}

procedure {:yields} {:layer 1} main({:linear_in "tid"} xls: [X]bool)
requires {:layer 1} xls == mapconstbool(true);
{
    var {:linear "tid"} tid: X;

    yield;

    call Init(xls);

    yield;
    assert {:layer 1} Inv(ghostLock, currsize, newsize);

    while (*)
    invariant {:layer 1} Inv(ghostLock, currsize, newsize);
    {
        par tid := Allocate() | Yield();
        yield;
        assert {:layer 1} Inv(ghostLock, currsize, newsize);
        async call Thread(tid);
        yield;
        assert {:layer 1} Inv(ghostLock, currsize, newsize);
    }
    yield;
}

procedure {:yields} {:layer 1} Thread({:linear "tid"} tid: X)
requires {:layer 1} tid != nil;
requires {:layer 1} Inv(ghostLock, currsize, newsize);
{
    var start, size, bytesRead: int;

    havoc start, size;
    assume (0 <= start && 0 <= size);
    call bytesRead := Read(tid, start, size);
}

procedure {:yields} {:layer 1} Read({:linear "tid"} tid: X, start : int, size : int) returns (bytesRead : int)
requires {:layer 1} tid != nil;
requires {:layer 1} 0 <= start && 0 <= size;
requires {:layer 1} Inv(ghostLock, currsize, newsize);
ensures {:layer 1} 0 <= bytesRead && bytesRead <= size;
{
    var i, tmp: int;

    par YieldToReadCache(tid);
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
    par YieldToWriteCache(tid);
    call WriteCache(tid, start + size);
    par YieldToWriteCache(tid);
    call acquire(tid);
    call tmp := ReadNewsize(tid);
    call WriteCurrsize(tid, tmp);
    call release(tid);

COPY_TO_BUFFER:
    par YieldToReadCache(tid);
    call ReadCache(tid, start, bytesRead);
}

procedure {:yields} {:layer 1} WriteCache({:linear "tid"} tid: X, index: int)
requires {:layer 1} Inv(ghostLock, currsize, newsize);
requires {:layer 1} ghostLock == tid && tid != nil;
ensures {:layer 1} ghostLock == tid;
ensures {:layer 1} Inv(ghostLock, currsize, newsize) && old(currsize) == currsize && old(newsize) == newsize;
{
    var j: int;

    par YieldToWriteCache(tid);
    call j := ReadCurrsize(tid);
    while (j < index)
    invariant {:layer 1} ghostLock == tid && currsize <= j && tid == tid;
    invariant {:layer 1} Inv(ghostLock, currsize, newsize) && old(currsize) == currsize && old(newsize) == newsize;
    {
        par YieldToWriteCache(tid);
        call WriteCacheEntry(tid, j);
        j := j + 1;
    }
    par YieldToWriteCache(tid);
}

procedure {:yields} {:layer 1} ReadCache({:linear "tid"} tid: X, start: int, bytesRead: int)
requires {:layer 1} Inv(ghostLock, currsize, newsize);
requires {:layer 1} tid != nil;
requires {:layer 1} 0 <= start && 0 <= bytesRead;
requires {:layer 1} (bytesRead == 0 || start + bytesRead <= currsize);
ensures {:layer 1} Inv(ghostLock, currsize, newsize);
{
    var j: int;

    par YieldToReadCache(tid);

    j := 0;
    while(j < bytesRead)
    invariant {:layer 1} 0 <= j;
    invariant {:layer 1} bytesRead == 0 || start + bytesRead <= currsize;
    invariant {:layer 1} Inv(ghostLock, currsize, newsize);
    {
        assert {:layer 1} start + j < currsize;
        call ReadCacheEntry(tid, start + j);
        j := j + 1;
        par YieldToReadCache(tid);
    }

    par YieldToReadCache(tid);
}

procedure {:atomic} {:layer 1} AtomicInit({:linear_in "tid"} xls:[X]bool)
modifies currsize, newsize, lock, ghostLock;
{ assert xls == mapconstbool(true); currsize := 0; newsize := 0; lock := nil; ghostLock := nil; }

procedure {:yields} {:layer 0} {:refines "AtomicInit"} Init({:linear_in "tid"} xls:[X]bool);

procedure {:right} {:layer 1} AtomicReadCurrsize({:linear "tid"} tid: X) returns (val: int)
{ assert tid != nil; assert lock == tid || ghostLock == tid; val := currsize; }

procedure {:yields} {:layer 0} {:refines "AtomicReadCurrsize"} ReadCurrsize({:linear "tid"} tid: X) returns (val: int);

procedure {:right} {:layer 1} AtomicReadNewsize({:linear "tid"} tid: X) returns (val: int)
{ assert tid != nil; assert lock == tid || ghostLock == tid; val := newsize; }

procedure {:yields} {:layer 0} {:refines "AtomicReadNewsize"} ReadNewsize({:linear "tid"} tid: X) returns (val: int);

procedure {:atomic} {:layer 1} AtomicWriteNewsize({:linear "tid"} tid: X, val: int)
modifies newsize, ghostLock;
{ assert tid != nil; assert lock == tid && ghostLock == nil; newsize := val; ghostLock := tid; }

procedure {:yields} {:layer 0} {:refines "AtomicWriteNewsize"} WriteNewsize({:linear "tid"} tid: X, val: int);

procedure {:atomic} {:layer 1} AtomicWriteCurrsize({:linear "tid"} tid: X, val: int)
modifies currsize, ghostLock;
{ assert tid != nil; assert lock == tid && ghostLock == tid; currsize := val; ghostLock := nil; }

procedure {:yields} {:layer 0} {:refines "AtomicWriteCurrsize"} WriteCurrsize({:linear "tid"} tid: X, val: int);

procedure {:atomic} {:layer 1} AtomicReadCacheEntry({:linear "tid"} tid: X, index: int)
{ assert 0 <= index && index < currsize; }

procedure {:yields} {:layer 0} {:refines "AtomicReadCacheEntry"} ReadCacheEntry({:linear "tid"} tid: X, index: int);

procedure {:right} {:layer 1} AtomicWriteCacheEntry({:linear "tid"} tid: X, index: int)
{ assert tid != nil; assert currsize <= index && ghostLock == tid; }

procedure {:yields} {:layer 0} {:refines "AtomicWriteCacheEntry"} WriteCacheEntry({:linear "tid"} tid: X, index: int);

procedure {:right} {:layer 1} atomic_acquire({:linear "tid"} tid: X)
modifies lock;
{ assert tid != nil; assume lock == nil; lock := tid; }

procedure {:yields} {:layer 0} {:refines "atomic_acquire"} acquire({:linear "tid"} tid: X);

procedure {:left} {:layer 1} atomic_release({:linear "tid"} tid: X)
modifies lock;
{ assert tid != nil; assert lock == tid; lock := nil; }

procedure {:yields} {:layer 0} {:refines "atomic_release"} release({:linear "tid"} tid: X);

procedure {:atomic} {:layer 1} AtomicAllocateLow() returns ({:linear "tid"} tid: X)
modifies unallocated;
{ assume tid != nil; assume unallocated[tid]; unallocated[tid] := false; }

procedure {:yields} {:layer 0} {:refines "AtomicAllocateLow"} AllocateLow() returns ({:linear "tid"} tid: X);
