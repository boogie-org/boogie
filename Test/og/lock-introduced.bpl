// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function {:builtin "MapConst"} MapConstBool(bool) : [X]bool;
function {:inline} {:linear "tid"} TidCollector(x: X) : [X]bool
{
  MapConstBool(false)[x := true]
}

type X;
const nil: X;
var {:phase 0,2} b: bool;
var {:phase 1,3} lock: X;

procedure {:yields} {:phase 3} Customer({:cnst "tid"} tid: X)
requires {:phase 2} tid != nil; 
requires {:phase 2} InvLock(lock, b);
ensures {:phase 2} InvLock(lock, b);
{
    yield;
    assert {:phase 2} InvLock(lock, b);
    while (*) 
    invariant {:phase 2} InvLock(lock, b);
    {
    	yield;
    	assert {:phase 2} InvLock(lock, b);

        call Enter(tid);

    	call Leave(tid);

        yield;
	assert {:phase 2} InvLock(lock, b);
    }
}

function {:inline} InvLock(lock: X, b: bool) : bool
{
    lock != nil <==> b
}

procedure {:yields} {:phase 2,3} Enter({:cnst "tid"} tid: X)
requires {:phase 2} tid != nil; 
requires {:phase 2} InvLock(lock, b);
ensures {:phase 2} InvLock(lock, b);
ensures {:right} |{ A: assume lock == nil && tid != nil; lock := tid; return true; }|;
{
    yield;
    assert {:phase 2} InvLock(lock, b);
    call LowerEnter(tid);
    yield;
    assert {:phase 2} InvLock(lock, b);
}

procedure {:yields} {:phase 2,3} Leave({:cnst "tid"} tid:X)
requires {:phase 2} InvLock(lock, b);
ensures {:phase 2} InvLock(lock, b);
ensures {:atomic} |{ A: assert lock == tid && tid != nil; lock := nil; return true; }|;
{
    yield;
    assert {:phase 2} InvLock(lock, b);
    call LowerLeave();
    yield;
    assert {:phase 2} InvLock(lock, b);
}

procedure {:yields} {:phase 1,2} LowerEnter({:cnst "tid"} tid: X) 
ensures {:atomic} |{ A: assume !b; b := true; lock := tid; return true; }|;
{
    var status: bool;
    yield;
    L: 
        call status := CAS(false, true);
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

procedure {:yields} {:phase 1,2} LowerLeave()
ensures {:atomic} |{ A: b := false; lock := nil; return true; }|;
{
    yield;
    call SET(false);
    yield;
}

procedure {:yields} {:phase 0,1} CAS(prev: bool, next: bool) returns (status: bool);
ensures {:atomic} |{ 
A: goto B, C; 
B: assume b == prev; b := next; status := true; return true; 
C: status := false; return true; 
}|;

procedure {:yields} {:phase 0,1} SET(next: bool);
ensures {:atomic} |{ A: b := next; return true; }|;

