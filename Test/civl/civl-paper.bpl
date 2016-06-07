// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
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

var {:layer 0,3} {:linear "mem"} g: lmap;
var {:layer 0,3} lock: X;
var {:layer 0,1} b: bool;

const p: int;

procedure {:yields} {:layer 1} Yield1()
requires {:layer 1} InvLock(lock, b);
ensures {:layer 1} InvLock(lock, b);
{
    yield;
    assert {:layer 1} InvLock(lock, b);
}

function {:inline} InvLock(lock: X, b: bool) : bool
{
    lock != nil <==> b
}

procedure {:yields} {:layer 2} Yield2()
{
    yield;
}

procedure {:yields} {:layer 3} Yield3()
requires {:layer 3} Inv(g);
ensures {:layer 3} Inv(g);
{
    yield;
    assert {:layer 3} Inv(g);
}

function {:inline} Inv(g: lmap) : bool
{
    dom(g)[p] && dom(g)[p+4] && map(g)[p] == map(g)[p+4]
}

procedure {:yields} {:layer 3} P({:linear "tid"} tid: X)
requires {:layer 1} tid != nil && InvLock(lock, b);
ensures {:layer 1} InvLock(lock, b);
requires {:layer 3} tid != nil && Inv(g);
ensures {:layer 3} Inv(g);
{
    var t: int;
    var {:linear "mem"} l: lmap;

    par Yield3() | Yield1();
    call AcquireProtected(tid);
    call l := TransferFromGlobalProtected(tid);
    call t := Load(l, p);
    call l := Store(l, p, t+1);
    call t := Load(l, p+4);
    call l := Store(l, p+4, t+1);
    call TransferToGlobalProtected(tid, l);
    call ReleaseProtected(tid);
    par Yield3() | Yield1();
}


procedure {:yields} {:layer 2,3} TransferToGlobalProtected({:linear "tid"} tid: X, {:linear_in "mem"} l: lmap)
ensures {:both} |{ A: assert tid != nil && lock == tid; g := l; return true; }|;
requires {:layer 1} InvLock(lock, b);
ensures {:layer 1} InvLock(lock, b);
{
  par Yield1() | Yield2();
  call TransferToGlobal(tid, l);
  par Yield1() | Yield2();
}

procedure {:yields} {:layer 2,3} TransferFromGlobalProtected({:linear "tid"} tid: X) returns ({:linear "mem"} l: lmap)
ensures {:both} |{ A: assert tid != nil && lock == tid; l := g; return true; }|;
requires {:layer 1} InvLock(lock, b);
ensures {:layer 1} InvLock(lock, b);
{
  par Yield1() | Yield2();
  call l := TransferFromGlobal(tid);
  par Yield1() | Yield2();
}

procedure {:yields} {:layer 2,3} AcquireProtected({:linear "tid"} tid: X)
ensures {:right} |{ A: assert tid != nil; assume lock == nil; lock := tid; return true; }|;
requires {:layer 1} tid != nil && InvLock(lock, b);
ensures {:layer 1} InvLock(lock, b);
{
  par Yield1() | Yield2();
  call Acquire(tid);
  par Yield1() | Yield2();
}

procedure {:yields} {:layer 2,3} ReleaseProtected({:linear "tid"} tid: X)
ensures {:left} |{ A: assert tid != nil && lock == tid; lock := nil; return true; }|;
requires {:layer 1} InvLock(lock, b);
ensures {:layer 1} InvLock(lock, b);
{
  par Yield1() | Yield2();
  call Release(tid);
  par Yield1() | Yield2();
}

procedure {:yields} {:layer 1,2} Acquire({:linear "tid"} tid: X)
requires {:layer 1} tid != nil && InvLock(lock, b);
ensures {:layer 1} InvLock(lock, b);
ensures {:atomic} |{ A: assume lock == nil; lock := tid; return true; }|;
{
    var status: bool;
    var tmp: X;

    par Yield1();
    L: 
	assert {:layer 1} InvLock(lock, b);
        call status := CAS(tid, false, true);
	par Yield1();
        goto A, B;

    A: 
        assume status;
	par Yield1();	
	return;

    B:
        assume !status;
	goto L;
}

procedure {:yields} {:layer 1,2} Release({:linear "tid"} tid: X)
ensures {:atomic} |{ A: lock := nil; return true; }|;
requires {:layer 1} InvLock(lock, b);
ensures {:layer 1} InvLock(lock, b);
{
    par Yield1();
    call CLEAR(tid, false);
    par Yield1();
}

procedure {:yields} {:layer 0,2} TransferToGlobal({:linear "tid"} tid: X, {:linear_in "mem"} l: lmap);
ensures {:atomic} |{ A: g := l; return true; }|;

procedure {:yields} {:layer 0,2} TransferFromGlobal({:linear "tid"} tid: X) returns ({:linear "mem"} l: lmap);
ensures {:atomic} |{ A: l := g; return true; }|;

procedure {:yields} {:layer 0,3} Load({:linear "mem"} l: lmap, a: int) returns (v: int);
ensures {:both} |{ A: v := map(l)[a]; return true; }|;

procedure {:yields} {:layer 0,3} Store({:linear_in "mem"} l_in: lmap, a: int, v: int) returns ({:linear "mem"} l_out: lmap);
ensures {:both} |{ A: assume l_out == cons(dom(l_in), map(l_in)[a := v]); return true; }|;

procedure {:yields} {:layer 0,1} CAS(tid: X, prev: bool, next: bool) returns (status: bool);
ensures {:atomic} |{ 
A: goto B, C; 
B: assume b == prev; b := next; status := true; lock := tid; return true; 
C: status := false; return true; 
}|;

procedure {:yields} {:layer 0,1} CLEAR(tid: X, next: bool);
ensures {:atomic} |{ 
A: b := next; lock := nil; return true; 
}|;

