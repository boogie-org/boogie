type X;
function {:builtin "MapConst"} mapconstbool(bool): [X]bool;
const nil: X;
var ghostLock: X;
var lock: X;
var currsize: int;
var newsize: int;

const device: [int]int;
var cache: [int]int;

function {:inline} Inv(ghostLock: X, currsize: int, newsize: int, cache: [int]int) : (bool)
{
    0 <= currsize && currsize <= newsize && 
    (ghostLock == nil <==> currsize == newsize) &&
    (forall i: int :: 0 <= i && i < currsize ==> device[i] == cache[i])
}

procedure {:stable} {:yields} YieldToReadCache()
requires Inv(ghostLock, currsize, newsize, cache);
ensures Inv(ghostLock, currsize, newsize, cache) && old(currsize) <= currsize;
{
}

procedure {:stable} {:yields} YieldToWriteCache({:linear "tid"} tid': X) returns ({:linear "tid"} tid: X)
requires Inv(ghostLock, currsize, newsize, cache) && ghostLock == tid' && tid' != nil;
ensures Inv(ghostLock, currsize, newsize, cache) && ghostLock == tid && tid != nil && tid == tid' && old(currsize) == currsize && old(newsize) == newsize;
{
    tid := tid';
}

procedure Allocate({:linear "tid"} xls': [X]bool) returns ({:linear "tid"} xls: [X]bool, {:linear "tid"} xl: X);
ensures xl != nil;

procedure {:entrypoint} {:yields} main({:linear "tid"} xls':[X]bool)
requires xls' == mapconstbool(true);
{
    var {:linear "tid"} tid: X;
    var {:linear "tid"} xls: [X]bool;

    call xls := Init(xls');

    while (*)
    invariant Inv(ghostLock, currsize, newsize, cache);
    {
        call xls, tid := Allocate(xls);
        async call Thread(tid);
    }
}

procedure {:yields} {:stable} Thread({:linear "tid"} tid': X)
requires tid' != nil;
requires Inv(ghostLock, currsize, newsize, cache);
{
    var start, size, bytesRead: int;
    var buffer: [int]int;
    var {:linear "tid"} tid: X;

    tid := tid';
    havoc start, size;
    assume (0 <= start && 0 <= size);
    call bytesRead, buffer := Read(tid, start, size);
}

procedure {:yields} Read({:linear "tid"} tid': X, start : int, size : int) returns (bytesRead : int, buffer : [int]int)
requires tid' != nil;
requires 0 <= start && 0 <= size;
requires Inv(ghostLock, currsize, newsize, cache);
ensures 0 <= bytesRead && bytesRead <= size;
ensures (forall i: int :: 0 <= i && i < bytesRead ==> buffer[i] == device[start+i]);
{
    var i, tmp: int;
    var {:linear "tid"} tid: X;
    tid := tid';

    yield;
    assert Inv(ghostLock, currsize, newsize, cache);
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
    call Skip() | tid := YieldToWriteCache(tid);
    call tid := WriteCache(tid, start + size);
    call tid := acquire(tid);
    call tid, tmp := ReadNewsize(tid);
    call tid := WriteCurrsize(tid, tmp);
    call tid := release(tid);

COPY_TO_BUFFER:
    call Skip() | YieldToReadCache();
    call buffer := ReadCache(start, bytesRead);
}

procedure {:yields} WriteCache({:linear "tid"} tid': X, index: int) returns ({:linear "tid"} tid: X)
ensures {:right 1} |{ A: assert ghostLock == tid' && tid' != nil; tid := tid'; cache := (lambda i: int :: if (currsize <= i && i < index) then device[i] else cache[i]); return true; }|;
{
    var j: int;
    tid := tid';

    call tid, j := ReadCurrsize(tid);
    while (j < index)
    invariant ghostLock == tid && currsize <= j && tid == tid';
    invariant cache == (lambda i: int :: if (currsize <= i && i < j) then device[i] else old(cache)[i]);
    {
        call tid := WriteCacheEntry(tid, j);
	j := j + 1;
    }
}

procedure {:yields} ReadCache(start: int, bytesRead: int) returns (buffer: [int]int)
requires 0 <= start && 0 <= bytesRead && (bytesRead == 0 || start + bytesRead <= currsize);
requires (forall i: int :: 0 <= i && i < currsize ==> cache[i] == device[i]);
ensures (forall i: int :: 0 <= i && i < bytesRead ==> buffer[i] == device[start+i]);
{
    var x: int;
    var j: int;
    j := 0;
    while(j < bytesRead)
    invariant bytesRead == 0 || start + j <= currsize; 
    invariant (forall i: int :: 0 <= i && i < j ==> buffer[i] == device[start+i]);
    {
	yield;
	assert start + j < currsize;
	assert (forall i: int :: 0 <= i && i < currsize ==> cache[i] == device[i]);
        call x := ReadCacheEntry(start + j);
	buffer[j] := x;
        j := j + 1;
    }
}

procedure {:yields} Init({:linear "tid"} xls':[X]bool) returns ({:linear "tid"} xls:[X]bool);
ensures {:both 0} |{ A: assert xls' == mapconstbool(true); xls := xls'; currsize := 0; newsize := 0; lock := nil; ghostLock := nil; return true; }|;

procedure {:yields} ReadCurrsize({:linear "tid"} tid': X) returns ({:linear "tid"} tid: X, val: int);
ensures {:right 0} |{A: assert tid' != nil; assert lock == tid' || ghostLock == tid'; tid := tid'; val := currsize; return true; }|;

procedure {:yields} ReadNewsize({:linear "tid"} tid': X) returns ({:linear "tid"} tid: X, val: int);
ensures {:right 0} |{A: assert tid' != nil; assert lock == tid' || ghostLock == tid'; tid := tid'; val := newsize; return true; }|;

procedure {:yields} WriteNewsize({:linear "tid"} tid': X, val: int) returns ({:linear "tid"} tid: X);
ensures {:atomic 0} |{A: assert tid' != nil; assert lock == tid' && ghostLock == nil; tid := tid'; newsize := val; ghostLock := tid; return true; }|;

procedure {:yields} WriteCurrsize({:linear "tid"} tid': X, val: int) returns ({:linear "tid"} tid: X);
ensures {:atomic 0} |{A: assert tid' != nil; assert lock == tid' && ghostLock == tid'; tid := tid'; currsize := val; ghostLock := nil; return true; }|;

procedure {:yields} ReadCacheEntry(index: int) returns (val: int);
ensures {:atomic 0} |{ A: assert 0 <= index && index < currsize; val := cache[index]; return true; }|;

procedure {:yields} WriteCacheEntry({:linear "tid"} tid': X, index: int) returns ({:linear "tid"} tid: X);
ensures {:right 0} |{ A: assert tid' != nil; assert currsize <= index && ghostLock == tid'; tid := tid'; cache[index] := device[index]; return true; }|;

procedure {:yields} acquire({:linear "tid"} tid': X) returns ({:linear "tid"} tid: X);
ensures {:right 0} |{ A: assert tid' != nil; tid := tid'; assume lock == nil; lock := tid; return true; }|;

procedure {:yields} release({:linear "tid"} tid': X) returns ({:linear "tid"} tid: X);
ensures {:left 0} |{ A: assert tid' != nil; assert lock == tid'; tid := tid'; lock := nil; return true; }|;

procedure {:yields} {:stable} Skip()
ensures {:both 0} |{ A: return true; }|;
{
}
