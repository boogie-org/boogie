// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function {:builtin "MapConst"} MapConstBool(bool) : [X]bool;
function {:inline} {:linear "tid"} TidCollector(x: X) : [X]bool
{
  MapConstBool(false)[x := true]
}

type X;
const nil: X;
var {:layer 0,2} b: bool;
var {:layer 1,3} lock: X;

procedure {:yields} {:layer 3} Customer({:linear "tid"} tid: X)
requires {:layer 2} tid != nil; 
requires {:layer 2} InvLock(lock, b);
ensures {:layer 2} InvLock(lock, b);
{
    yield;
    assert {:layer 2} InvLock(lock, b);
    while (*) 
    invariant {:layer 2} InvLock(lock, b);
    {
        call Enter(tid);
    	call Leave(tid);
        yield;
	assert {:layer 2} InvLock(lock, b);
    }    
    yield;
    assert {:layer 2} InvLock(lock, b);
}

function {:inline} InvLock(lock: X, b: bool) : bool
{
    lock != nil <==> b
}

procedure {:yields} {:layer 2,3} Enter({:linear "tid"} tid: X)
requires {:layer 2} tid != nil; 
requires {:layer 2} InvLock(lock, b);
ensures {:layer 2} InvLock(lock, b);
ensures {:right} |{ A: assume lock == nil && tid != nil; lock := tid; return true; }|;
{
    yield;
    assert {:layer 2} InvLock(lock, b);
    call LowerEnter(tid);
    yield;
    assert {:layer 2} InvLock(lock, b);
}

procedure {:yields} {:layer 2,3} Leave({:linear "tid"} tid:X)
requires {:layer 2} InvLock(lock, b);
ensures {:layer 2} InvLock(lock, b);
ensures {:atomic} |{ A: assert lock == tid && tid != nil; lock := nil; return true; }|;
{
    yield;
    assert {:layer 2} InvLock(lock, b);
    call LowerLeave();
    yield;
    assert {:layer 2} InvLock(lock, b);
}

procedure {:yields} {:layer 1,2} LowerEnter({:linear "tid"} tid: X) 
ensures {:atomic} |{ A: assume !b; b := true; lock := tid; return true; }|;
{
    var status: bool;
    yield;
    L: 
        call status := CAS(false, true);
        if (status) {
	    call SetLock(tid);
	}
	yield;
        goto A, B;

    A: 
        assume status;
	yield;
	return;

    B:
        assume !status;
	goto L;
}

procedure {:yields} {:layer 1,2} LowerLeave()
ensures {:atomic} |{ A: b := false; lock := nil; return true; }|;
{
    yield;
    call SET(false);
    call SetLock(nil);
    yield;
}

procedure {:layer 1} {:inline 1} SetLock(v: X)
modifies lock;
{
    lock := v;
}

procedure {:yields} {:layer 0,1} CAS(prev: bool, next: bool) returns (status: bool);
ensures {:atomic} |{ 
A: goto B, C; 
B: assume b == prev; b := next; status := true; return true; 
C: status := false; return true; 
}|;

procedure {:yields} {:layer 0,1} SET(next: bool);
ensures {:atomic} |{ A: b := next; return true; }|;

