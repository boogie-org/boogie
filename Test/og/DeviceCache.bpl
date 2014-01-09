type X;
function {:builtin "MapConst"} mapconstbool(bool): [X]bool;
const nil: X;
var {:qed} ghostLock: X;
var {:qed} lock: X;
var {:qed} currsize: int;
var {:qed} newsize: int;

function {:inline} Inv(ghostLock: X, currsize: int, newsize: int) : (bool)
{
    0 <= currsize && currsize <= newsize && 
    (ghostLock == nil <==> currsize == newsize)
}

procedure {:stable} {:yields} YieldToReadCache({:linear "tid"} tid': X) returns ({:linear "tid"} tid: X)
requires {:phase 1} Inv(ghostLock, currsize, newsize) && tid' != nil;
ensures {:phase 1} Inv(ghostLock, currsize, newsize) && tid != nil && tid == tid' && old(currsize) <= currsize;
{
   tid := tid';
}

procedure {:stable} {:yields} YieldToWriteCache({:linear "tid"} tid': X) returns ({:linear "tid"} tid: X)
requires {:phase 1} Inv(ghostLock, currsize, newsize) && ghostLock == tid' && tid' != nil;
ensures {:phase 1} Inv(ghostLock, currsize, newsize) && ghostLock == tid && tid != nil && tid == tid' && old(currsize) == currsize && old(newsize) == newsize;
{
    tid := tid';
}

procedure Allocate({:linear "tid"} xls': [X]bool) returns ({:linear "tid"} xls: [X]bool, {:linear "tid"} xl: X);
ensures {:phase 1} xl != nil;

procedure {:entrypoint} {:yields} main({:linear "tid"} xls':[X]bool)
requires {:phase 1} xls' == mapconstbool(true);
{
    var {:linear "tid"} tid: X;
    var {:linear "tid"} xls: [X]bool;

    yield;

    call xls := Init(xls');
    
    yield;
    assert {:phase 1} Inv(ghostLock, currsize, newsize);

    while (*)
    invariant {:phase 1} Inv(ghostLock, currsize, newsize);
    {
        call xls, tid := Allocate(xls);
        async call Thread(tid);
    }
}

procedure {:yields} {:stable} Thread({:linear "tid"} tid': X)
requires {:phase 1} tid' != nil;
requires {:phase 1} Inv(ghostLock, currsize, newsize);
{
    var start, size, bytesRead: int;
    var {:linear "tid"} tid: X;

    tid := tid';
    havoc start, size;
    assume (0 <= start && 0 <= size);
    call bytesRead := Read(tid, start, size);
}

procedure {:yields} Read({:linear "tid"} tid': X, start : int, size : int) returns (bytesRead : int)
requires {:phase 1} tid' != nil;
requires {:phase 1} 0 <= start && 0 <= size;
requires {:phase 1} Inv(ghostLock, currsize, newsize);
ensures {:phase 1} 0 <= bytesRead && bytesRead <= size;
{
    var i, tmp: int;
    var {:linear "tid"} tid: X;
    tid := tid';

    par  tid := YieldToReadCache(tid);
    bytesRead := size;
    call tid := acquire(tid);
    call tid, i := ReadCurrsize(tid);
    call tid, tmp := ReadNewsize(tid);
    if (start + size <= i) {
        call tid := release(tid); 
    	goto COPY_TO_BUFFER;
    } else if (tmp > i) {
        bytesRead := if (start <= i) then (i - start) else 0;
    	call tid := release(tid); 
	goto COPY_TO_BUFFER;
    } else {
        call tid := WriteNewsize(tid, start + size);
    	call tid := release(tid); 
	goto READ_DEVICE;
    }

READ_DEVICE:
    par  tid := YieldToWriteCache(tid);
    call tid := WriteCache(tid, start + size);
    par  tid := YieldToReadCache(tid);
    call tid := acquire(tid);
    call tid, tmp := ReadNewsize(tid);
    call tid := WriteCurrsize(tid, tmp);
    call tid := release(tid);

COPY_TO_BUFFER:
    par tid := YieldToReadCache(tid);
    call tid := ReadCache(tid, start, bytesRead);
}

procedure {:yields} WriteCache({:linear "tid"} tid': X, index: int) returns ({:linear "tid"} tid: X)
requires {:phase 1} Inv(ghostLock, currsize, newsize);
requires {:phase 1} ghostLock == tid' && tid' != nil;
ensures {:phase 1} tid == tid' && ghostLock == tid;
ensures {:phase 1} Inv(ghostLock, currsize, newsize) && old(currsize) == currsize && old(newsize) == newsize;
{
    var j: int;
    tid := tid';

    par tid := YieldToWriteCache(tid);
    call tid, j := ReadCurrsize(tid);
    while (j < index)
    invariant {:phase 1} ghostLock == tid && currsize <= j && tid == tid';
    invariant {:phase 1} Inv(ghostLock, currsize, newsize) && old(currsize) == currsize && old(newsize) == newsize;
    {
        par tid := YieldToWriteCache(tid);
        call tid := WriteCacheEntry(tid, j);
	j := j + 1;
    }
    par tid := YieldToWriteCache(tid);
}

procedure {:yields} ReadCache({:linear "tid"} tid': X, start: int, bytesRead: int) returns ({:linear "tid"} tid: X)
requires {:phase 1} Inv(ghostLock, currsize, newsize);
requires {:phase 1} tid' != nil;
requires {:phase 1} 0 <= start && 0 <= bytesRead;
requires {:phase 1} (bytesRead == 0 || start + bytesRead <= currsize);
ensures {:phase 1} tid == tid';
ensures {:phase 1} Inv(ghostLock, currsize, newsize);
{
    var j: int;
    tid := tid';

    par tid := YieldToReadCache(tid);

    j := 0;
    while(j < bytesRead)
    invariant {:phase 1} 0 <= j;
    invariant {:phase 1} bytesRead == 0 || start + j <= currsize; 
    invariant {:phase 1} Inv(ghostLock, currsize, newsize) && tid == tid';
    {
	assert {:phase 1} start + j < currsize;
        call tid := ReadCacheEntry(tid, start + j);
        j := j + 1;
	par tid := YieldToReadCache(tid);
    }
}

procedure {:yields} Init({:linear "tid"} xls':[X]bool) returns ({:linear "tid"} xls:[X]bool);
ensures {:atomic 0} |{ A: assert xls' == mapconstbool(true); xls := xls'; currsize := 0; newsize := 0; lock := nil; ghostLock := nil; return true; }|;

procedure {:yields} ReadCurrsize({:linear "tid"} tid': X) returns ({:linear "tid"} tid: X, val: int);
ensures {:right 0} |{A: assert tid' != nil; assert lock == tid' || ghostLock == tid'; tid := tid'; val := currsize; return true; }|;

procedure {:yields} ReadNewsize({:linear "tid"} tid': X) returns ({:linear "tid"} tid: X, val: int);
ensures {:right 0} |{A: assert tid' != nil; assert lock == tid' || ghostLock == tid'; tid := tid'; val := newsize; return true; }|;

procedure {:yields} WriteNewsize({:linear "tid"} tid': X, val: int) returns ({:linear "tid"} tid: X);
ensures {:atomic 0} |{A: assert tid' != nil; assert lock == tid' && ghostLock == nil; tid := tid'; newsize := val; ghostLock := tid; return true; }|;

procedure {:yields} WriteCurrsize({:linear "tid"} tid': X, val: int) returns ({:linear "tid"} tid: X);
ensures {:atomic 0} |{A: assert tid' != nil; assert lock == tid' && ghostLock == tid'; tid := tid'; currsize := val; ghostLock := nil; return true; }|;

procedure {:yields} ReadCacheEntry({:linear "tid"} tid': X, index: int) returns ({:linear "tid"} tid: X);
ensures {:atomic 0} |{ A: assert 0 <= index && index < currsize; tid := tid'; return true; }|;

procedure {:yields} WriteCacheEntry({:linear "tid"} tid': X, index: int) returns ({:linear "tid"} tid: X);
ensures {:right 0} |{ A: assert tid' != nil; assert currsize <= index && ghostLock == tid'; tid := tid'; return true; }|;

procedure {:yields} acquire({:linear "tid"} tid': X) returns ({:linear "tid"} tid: X);
ensures {:right 0} |{ A: assert tid' != nil; tid := tid'; assume lock == nil; lock := tid; return true; }|;

procedure {:yields} release({:linear "tid"} tid': X) returns ({:linear "tid"} tid: X);
ensures {:left 0} |{ A: assert tid' != nil; assert lock == tid'; tid := tid'; lock := nil; return true; }|;
