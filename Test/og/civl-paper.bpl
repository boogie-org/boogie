type X;
const nil: X;

function {:builtin "MapConst"} MapConstBool(bool) : [X]bool;
function {:inline} {:linear "tid"} TidCollector(x: X) : [X]bool
{
  MapConstBool(false)[x := true]
}

type lmap;
function {:linear "mem"} dom(lmap): [int]bool;
function map(lmap): [int]int;
function cons([int]bool, [int]int) : lmap;
axiom (forall x: [int]bool, y: [int]int :: {cons(x,y)} dom(cons(x, y)) == x && map(cons(x,y)) == y);

var {:phase 2} {:linear "mem"} g: lmap;

const p: int;

procedure {:yields} {:phase 1,2} TransferToGlobal({:cnst "tid"} tid: X, {:linear "mem"} l: lmap);
ensures {:both} |{ A: assert tid != nil && lock == tid; g := l; return true; }|;
requires {:phase 1} InvLock(lock, b);
ensures {:phase 1} InvLock(lock, b);

procedure {:yields} {:phase 1,2} TransferFromGlobal({:cnst "tid"} tid: X) returns ({:linear "mem"} l: lmap);
ensures {:both} |{ A: assert tid != nil && lock == tid; l := g; return true; }|;
requires {:phase 1} InvLock(lock, b);
ensures {:phase 1} InvLock(lock, b);

procedure {:yields} {:phase 1} Load({:cnst "mem"} l: lmap, a: int) returns (v: int);
ensures {:both} |{ A: v := map(l)[a]; return true; }|;
requires {:phase 1} InvLock(lock, b);
ensures {:phase 1} InvLock(lock, b);

procedure {:yields} {:phase 1} Store({:linear "mem"} l_in: lmap, a: int, v: int) returns ({:linear "mem"} l_out: lmap);
ensures {:both} |{ A: assume l_out == cons(dom(l_in), map(l_in)[a := v]); return true; }|;
requires {:phase 1} InvLock(lock, b);
ensures {:phase 1} InvLock(lock, b);

procedure {:yields} {:phase 2} P({:cnst "tid"} tid: X)
requires {:phase 1} InvLock(lock, b);
ensures {:phase 1} InvLock(lock, b);
requires {:phase 2} tid != nil && Inv(g);
ensures {:phase 2} Inv(g);
{
    var t: int;
    var {:linear "mem"} l: lmap;

    par Yield() | YieldLock();
    call Acquire(tid);
    call l := TransferFromGlobal(tid);
    call t := Load(l, p);
    call l := Store(l, p, t+1);
    call t := Load(l, p+4);
    call l := Store(l, p+4, t+1);
    call TransferToGlobal(tid, l);
    call Release(tid);
    par Yield() | YieldLock();
}

procedure {:yields} {:phase 2} Yield()
requires {:phase 2} Inv(g);
ensures {:phase 2} Inv(g);
{
    yield;
    assert {:phase 2} Inv(g);
}

function {:inline} Inv(g: lmap) : bool
{
    dom(g)[p] && dom(g)[p+4] && map(g)[p] == map(g)[p+4]
}


var {:phase 1} b: bool;
var {:phase 2} lock: X;

procedure {:yields} {:phase 1,2} Acquire({:cnst "tid"} tid: X)
requires {:phase 1} InvLock(lock, b);
ensures {:phase 1} InvLock(lock, b);
ensures {:right} |{ A: assert tid != nil; assume lock == nil; lock := tid; return true; }|;
{
    var status: bool;
    var tmp: X;

    par YieldLock();
    L: 
	assert {:phase 1} InvLock(lock, b);
        call status := CAS(tid, false, true);
	par YieldLock();
        goto A, B;

    A: 
        assume status;
	par YieldLock();	
	return;

    B:
        assume !status;
	goto L;
}

procedure {:yields} {:phase 1,2} Release({:cnst "tid"} tid: X)
ensures {:left} |{ A: assert lock == tid && tid != nil; lock := nil; return true; }|;
requires {:phase 1} InvLock(lock, b);
ensures {:phase 1} InvLock(lock, b);
{
    par YieldLock();
    call CLEAR(tid, false);
    par YieldLock();
}

procedure {:yields} {:phase 0,1} CAS(tid: X, prev: bool, next: bool) returns (status: bool);
ensures {:atomic} |{ 
A: goto B, C; 
B: assume b == prev; b := next; status := true; lock := tid; return true; 
C: status := false; return true; 
}|;

procedure {:yields} {:phase 0,1} CLEAR(tid: X, next: bool);
ensures {:atomic} |{ 
A: b := next; lock := nil; return true; 
}|;

procedure {:yields} {:phase 1} YieldLock()
requires {:phase 1} InvLock(lock, b);
ensures {:phase 1} InvLock(lock, b);
{
    yield;
    assert {:phase 1} InvLock(lock, b);
}

function {:inline} InvLock(lock: X, b: bool) : bool
{
    lock != nil <==> b
}
