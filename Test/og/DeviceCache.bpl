type X;
function {:builtin "MapConst"} mapconstbool(bool): [X]bool;
const nil: X;
var {:phase 1} ghostLock: X;
var {:phase 1} lock: X;
var {:phase 1} currsize: int;
var {:phase 1} newsize: int;

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

procedure {:yields} {:phase 1} YieldToReadCache({:cnst "tid"} tid: X)
requires {:phase 1} Inv(ghostLock, currsize, newsize) && tid != nil;
ensures {:phase 1} Inv(ghostLock, currsize, newsize) && old(currsize) <= currsize;
{
   yield;
   assert {:phase 1} Inv(ghostLock, currsize, newsize) && old(currsize) <= currsize;
}

procedure {:yields} {:phase 1} YieldToWriteCache({:cnst "tid"} tid: X)
requires {:phase 1} Inv(ghostLock, currsize, newsize) && ghostLock == tid && tid != nil;
ensures {:phase 1} Inv(ghostLock, currsize, newsize) && ghostLock == tid && old(currsize) == currsize && old(newsize) == newsize;
{
    yield;
    assert {:phase 1} Inv(ghostLock, currsize, newsize) && tid != nil && ghostLock == tid && old(currsize) == currsize && old(newsize) == newsize;
}

procedure Allocate({:linear "tid"} xls': [X]bool) returns ({:linear "tid"} xls: [X]bool, {:linear "tid"} xl: X);
ensures {:phase 1} xl != nil;

procedure {:yields} {:phase 1} main({:linear "tid"} xls':[X]bool)
requires {:phase 1} xls' == mapconstbool(true);
{
    var {:linear "tid"} tid: X;
    var {:linear "tid"} xls: [X]bool;

    yield;

    xls := xls';
    call Init(xls);
    
    yield;
    assert {:phase 1} Inv(ghostLock, currsize, newsize);

    while (*)
    invariant {:phase 1} Inv(ghostLock, currsize, newsize);
    {
        call xls, tid := Allocate(xls);
	yield;
    	assert {:phase 1} Inv(ghostLock, currsize, newsize);
        async call Thread(tid);
	yield;
    	assert {:phase 1} Inv(ghostLock, currsize, newsize);
    }
}

procedure {:yields} {:phase 1} Thread({:cnst "tid"} tid: X)
requires {:phase 1} tid != nil;
requires {:phase 1} Inv(ghostLock, currsize, newsize);
{
    var start, size, bytesRead: int;

    havoc start, size;
    assume (0 <= start && 0 <= size);
    call bytesRead := Read(tid, start, size);
}

procedure {:yields} {:phase 1} Read({:cnst "tid"} tid: X, start : int, size : int) returns (bytesRead : int)
requires {:phase 1} tid != nil;
requires {:phase 1} 0 <= start && 0 <= size;
requires {:phase 1} Inv(ghostLock, currsize, newsize);
ensures {:phase 1} 0 <= bytesRead && bytesRead <= size;
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

procedure {:yields} {:phase 1} WriteCache({:cnst "tid"} tid: X, index: int)
requires {:phase 1} Inv(ghostLock, currsize, newsize);
requires {:phase 1} ghostLock == tid && tid != nil;
ensures {:phase 1} ghostLock == tid;
ensures {:phase 1} Inv(ghostLock, currsize, newsize) && old(currsize) == currsize && old(newsize) == newsize;
{
    var j: int;

    par YieldToWriteCache(tid);
    call j := ReadCurrsize(tid);
    while (j < index)
    invariant {:phase 1} ghostLock == tid && currsize <= j && tid == tid;
    invariant {:phase 1} Inv(ghostLock, currsize, newsize) && old(currsize) == currsize && old(newsize) == newsize;
    {
        par YieldToWriteCache(tid);
        call WriteCacheEntry(tid, j);
	j := j + 1;
    }
    par YieldToWriteCache(tid);
}

procedure {:yields} {:phase 1} ReadCache({:cnst "tid"} tid: X, start: int, bytesRead: int)
requires {:phase 1} Inv(ghostLock, currsize, newsize);
requires {:phase 1} tid != nil;
requires {:phase 1} 0 <= start && 0 <= bytesRead;
requires {:phase 1} (bytesRead == 0 || start + bytesRead <= currsize);
ensures {:phase 1} Inv(ghostLock, currsize, newsize);
{
    var j: int;

    par YieldToReadCache(tid);

    j := 0;
    while(j < bytesRead)
    invariant {:phase 1} 0 <= j;
    invariant {:phase 1} bytesRead == 0 || start + bytesRead <= currsize; 
    invariant {:phase 1} Inv(ghostLock, currsize, newsize);
    {
	assert {:phase 1} start + j < currsize;
        call ReadCacheEntry(tid, start + j);
        j := j + 1;
	par YieldToReadCache(tid);
    }

    par YieldToReadCache(tid);
}

procedure {:yields} {:phase 0,1} Init({:cnst "tid"} xls:[X]bool);
ensures {:atomic} |{ A: assert xls == mapconstbool(true); currsize := 0; newsize := 0; lock := nil; ghostLock := nil; return true; }|;

procedure {:yields} {:phase 0,1} ReadCurrsize({:cnst "tid"} tid: X) returns (val: int);
ensures {:right} |{A: assert tid != nil; assert lock == tid || ghostLock == tid; val := currsize; return true; }|;

procedure {:yields} {:phase 0,1} ReadNewsize({:cnst "tid"} tid: X) returns (val: int);
ensures {:right} |{A: assert tid != nil; assert lock == tid || ghostLock == tid; val := newsize; return true; }|;

procedure {:yields} {:phase 0,1} WriteNewsize({:cnst "tid"} tid: X, val: int);
ensures {:atomic} |{A: assert tid != nil; assert lock == tid && ghostLock == nil; newsize := val; ghostLock := tid; return true; }|;

procedure {:yields} {:phase 0,1} WriteCurrsize({:cnst "tid"} tid: X, val: int);
ensures {:atomic} |{A: assert tid != nil; assert lock == tid && ghostLock == tid; currsize := val; ghostLock := nil; return true; }|;

procedure {:yields} {:phase 0,1} ReadCacheEntry({:cnst "tid"} tid: X, index: int);
ensures {:atomic} |{ A: assert 0 <= index && index < currsize; return true; }|;

procedure {:yields} {:phase 0,1} WriteCacheEntry({:cnst "tid"} tid: X, index: int);
ensures {:right} |{ A: assert tid != nil; assert currsize <= index && ghostLock == tid; return true; }|;

procedure {:yields} {:phase 0,1} acquire({:cnst "tid"} tid: X);
ensures {:right} |{ A: assert tid != nil; assume lock == nil; lock := tid; return true; }|;

procedure {:yields} {:phase 0,1} release({:cnst "tid"} tid: X);
ensures {:left} |{ A: assert tid != nil; assert lock == tid; lock := nil; return true; }|;
