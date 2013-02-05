function {:inline} Inv1(currsize: int, newsize: int) : (bool)
{
    currsize <= newsize
}

function {:inline} Inv2(ghostLock: X, currsize: int, newsize: int) : (bool)
{
    ghostLock == nil <==> currsize == newsize
}

procedure Yield({:linear "tid"} tid': X) returns ({:linear "tid"} tid: X)
requires tid' != nil;
ensures tid == tid';
requires Inv1(currsize, newsize);
requires Inv2(ghostLock, currsize, newsize);
ensures Inv1(currsize, newsize);
ensures Inv2(ghostLock, currsize, newsize);
{
    assume tid == tid';
    assert {:yield} Inv1(currsize, newsize);
    assert Inv2(ghostLock, currsize, newsize);
    assert tid != nil;
}

procedure YieldWithGhostLock({:linear "tid"} tid': X) returns ({:linear "tid"} tid: X)
requires tid' != nil;
ensures tid == tid';
requires Inv1(currsize, newsize);
requires Inv2(ghostLock, currsize, newsize);
requires ghostLock == tid';
ensures Inv1(currsize, newsize);
ensures Inv2(ghostLock, currsize, newsize);
ensures ghostLock == tid;
{
    assume tid == tid';
    assert {:yield} Inv1(currsize, newsize);
    assert Inv2(ghostLock, currsize, newsize);
    assert tid != nil;
    assert ghostLock == tid;
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
requires Inv1(currsize, newsize);
requires Inv2(ghostLock, currsize, newsize);
ensures 0 <= bytesread && bytesread <= size;
{
    var copyGhostLock: X;
    var i, j, tmp : int;
    var {:linear "tid"} tid: X;
    assume tid == tid';

    bytesread := size;
    call acquire(tid);
    i := currsize;
    if (start + size <= i) {
        call release(tid); 
	call tid := Yield(tid);
	goto COPY_TO_BUFFER;
    } else if (newsize > i) {
        bytesread := if (start <= i) then (i - start) else 0;
	call release(tid); 
	call tid := Yield(tid);
	goto COPY_TO_BUFFER;
    } else {
        newsize := start + size;
	ghostLock := tid;
	call release(tid); 
	call tid := YieldWithGhostLock(tid);
	goto READ_DEVICE;
    }

READ_DEVICE:
    while (i < start + size) 
    invariant Inv1(currsize, newsize);
    invariant Inv2(ghostLock, currsize, newsize); 
    invariant ghostLock == tid;
    invariant tid != nil;
    {
        assert ghostLock == tid;
        call tid := YieldWithGhostLock(tid);
	i := i + 1;
    }
    call acquire(tid);
    tmp := newsize;
    currsize := tmp;
    ghostLock := nil;
    call release(tid);
    call tid := Yield(tid);

COPY_TO_BUFFER:
    j := 0;
    while(j < bytesread) 
    invariant Inv1(currsize, newsize);
    invariant Inv2(ghostLock, currsize, newsize); 
    invariant tid != nil;
    {
        call tid := Yield(tid);
        j := j + 1;
    }
}

procedure thread({:linear "tid"} tid': X)
requires tid' != nil;
requires Inv1(currsize, newsize);
requires Inv2(ghostLock, currsize, newsize);
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