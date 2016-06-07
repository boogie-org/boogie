// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type X;
function {:builtin "MapConst"} mapconstbool(bool): [X]bool;
const nil: X;
var {:layer 0,1} ghostLock: X;
var {:layer 0,1} lock: X;
var {:layer 0,1} currsize: int;
var {:layer 0,1} newsize: int;

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

procedure {:yields} {:layer 0,1} Init({:linear_in "tid"} xls:[X]bool);
ensures {:atomic} |{ A: assert xls == mapconstbool(true); currsize := 0; newsize := 0; lock := nil; ghostLock := nil; return true; }|;

procedure {:yields} {:layer 0,1} ReadCurrsize({:linear "tid"} tid: X) returns (val: int);
ensures {:right} |{A: assert tid != nil; assert lock == tid || ghostLock == tid; val := currsize; return true; }|;

procedure {:yields} {:layer 0,1} ReadNewsize({:linear "tid"} tid: X) returns (val: int);
ensures {:right} |{A: assert tid != nil; assert lock == tid || ghostLock == tid; val := newsize; return true; }|;

procedure {:yields} {:layer 0,1} WriteNewsize({:linear "tid"} tid: X, val: int);
ensures {:atomic} |{A: assert tid != nil; assert lock == tid && ghostLock == nil; newsize := val; ghostLock := tid; return true; }|;

procedure {:yields} {:layer 0,1} WriteCurrsize({:linear "tid"} tid: X, val: int);
ensures {:atomic} |{A: assert tid != nil; assert lock == tid && ghostLock == tid; currsize := val; ghostLock := nil; return true; }|;

procedure {:yields} {:layer 0,1} ReadCacheEntry({:linear "tid"} tid: X, index: int);
ensures {:atomic} |{ A: assert 0 <= index && index < currsize; return true; }|;

procedure {:yields} {:layer 0,1} WriteCacheEntry({:linear "tid"} tid: X, index: int);
ensures {:right} |{ A: assert tid != nil; assert currsize <= index && ghostLock == tid; return true; }|;

procedure {:yields} {:layer 0,1} acquire({:linear "tid"} tid: X);
ensures {:right} |{ A: assert tid != nil; assume lock == nil; lock := tid; return true; }|;

procedure {:yields} {:layer 0,1} release({:linear "tid"} tid: X);
ensures {:left} |{ A: assert tid != nil; assert lock == tid; lock := nil; return true; }|;

procedure {:yields} {:layer 0,1} AllocateLow() returns ({:linear "tid"} tid: X);
ensures {:atomic} |{ A: assume tid != nil; return true; }|;
