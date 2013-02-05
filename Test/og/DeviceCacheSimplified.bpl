function {:inline} Inv(ghostLock: X, currsize: int, newsize: int) : (bool)
{
    currsize <= newsize && (ghostLock == nil <==> currsize == newsize)
}

procedure YieldToReadCache({:linear "tid"} tid': X) returns ({:linear "tid"} tid: X)
requires tid' != nil;
requires Inv(ghostLock, currsize, newsize);
ensures Inv(ghostLock, currsize, newsize);
ensures old(currsize) <= currsize;
ensures tid == tid';
{
    assume tid == tid';
    assert {:yield} Inv(ghostLock, currsize, newsize);
    assert old(currsize) <= currsize;
    assert tid != nil;
}

procedure YieldToUpdateCache({:linear "tid"} tid': X, i: int) returns ({:linear "tid"} tid: X)
requires tid' != nil;
requires Inv(ghostLock, currsize, newsize);
requires ghostLock == tid';
requires currsize <= i;
ensures Inv(ghostLock, currsize, newsize);
ensures old(currsize) <= currsize;
ensures tid == tid';
ensures ghostLock == tid;
ensures currsize <= i;
ensures newsize == old(newsize);
{
    assume tid == tid';
    assert {:yield} Inv(ghostLock, currsize, newsize);
    assert old(currsize) <= currsize;
    assert tid != nil;
    assert ghostLock == tid;
    assert currsize <= i;
    assert newsize == old(newsize);
}

var ghostLock: X;
var lock: X;
const nil: X;
var currsize: int;
var newsize: int;

procedure acquire(tid: X);
modifies lock;
ensures old(lock) == nil && lock == tid;

procedure release(tid: X);
modifies lock;
requires lock == tid;
ensures lock == nil;

procedure Read ({:linear "tid"} tid': X, start : int, size : int) returns (bytesread : int)
requires tid' != nil;
requires 0 <= start && 0 <= size;
requires Inv(ghostLock, currsize, newsize);
ensures 0 <= bytesread && bytesread <= size;
{
    var copy_currsize: int;
    var i, j, tmp : int;
    var {:linear "tid"} tid: X;
    assume tid == tid';

    bytesread := size;
    call acquire(tid);
    i := currsize;
    if (start + size <= i) {
        call release(tid); 
	call tid := YieldToReadCache(tid);
	goto COPY_TO_BUFFER;
    } else if (newsize > i) {
        bytesread := if (start <= i) then (i - start) else 0;
	call release(tid); 
	call tid := YieldToReadCache(tid);
	goto COPY_TO_BUFFER;
    } else {
        newsize := start + size;
	ghostLock := tid;
	call release(tid); 
	call tid := YieldToUpdateCache(tid, i);
	goto READ_DEVICE;
    }

READ_DEVICE:
    while (i < start + size) 
    invariant Inv(ghostLock, currsize, newsize); 
    invariant ghostLock == tid;
    invariant tid != nil;
    invariant currsize <= i;
    invariant newsize == start + size;
    {
        call tid := YieldToUpdateCache(tid, i);
	assert currsize <= i;
	i := i + 1;
    }
    call acquire(tid);
    tmp := newsize;
    currsize := tmp;
    ghostLock := nil;
    call release(tid);
    call tid := YieldToReadCache(tid);

COPY_TO_BUFFER:
    j := 0;
    while(j < bytesread) 
    invariant 0 <= j;
    invariant Inv(ghostLock, currsize, newsize); 
    invariant tid != nil;
    invariant bytesread == 0 || start + bytesread <= currsize;
    {
        call tid := YieldToReadCache(tid);
	assert start + j < currsize;
        j := j + 1;
    }
}

procedure thread({:linear "tid"} tid': X)
requires tid' != nil;
requires Inv(ghostLock, currsize, newsize);
{
    var start, size, bytesread: int;
    var {:linear "tid"} tid: X;

    assume tid == tid';
    havoc start, size;
    assume (0 <= start && 0 <= size);
    call bytesread := Read(tid, start, size);
}

procedure {:entrypoint} main()
requires currsize == 0 && newsize == 0 && ghostLock == nil && lock == nil;
{
    var {:linear "tid"} tid: X;

    while (*)
    {
        havoc tid;
	assume tid != nil;
        call {:async} thread(tid);
    }
}