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

function emptyDom(l:lmap) : lmap
{ cons((lambda x:int :: false), map(l)) }

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

procedure {:both} {:layer 3} AtomicTransferToGlobalProtected({:linear "tid"} tid: X, {:linear_in "mem"} l: lmap)
modifies g;
{ assert tid != nil && lock == tid; g := l; }

procedure {:yields} {:layer 2} {:refines "AtomicTransferToGlobalProtected"} TransferToGlobalProtected({:linear "tid"} tid: X, {:linear_in "mem"} l: lmap)
requires {:layer 1} InvLock(lock, b);
ensures {:layer 1} InvLock(lock, b);
{
  par Yield1() | Yield2();
  call TransferToGlobal(tid, l);
  par Yield1() | Yield2();
}

procedure {:both} {:layer 3} AtomicTransferFromGlobalProtected({:linear "tid"} tid: X) returns ({:linear "mem"} l: lmap)
modifies g;
{ assert tid != nil && lock == tid; l := g; g := emptyDom(g); }

procedure {:yields} {:layer 2} {:refines "AtomicTransferFromGlobalProtected"} TransferFromGlobalProtected({:linear "tid"} tid: X) returns ({:linear "mem"} l: lmap)
requires {:layer 1} InvLock(lock, b);
ensures {:layer 1} InvLock(lock, b);
{
  par Yield1() | Yield2();
  call l := TransferFromGlobal(tid);
  par Yield1() | Yield2();
}

procedure {:right} {:layer 3} AtomicAcquireProtected({:linear "tid"} tid: X)
modifies lock;
{ assert tid != nil; assume lock == nil; lock := tid; }

procedure {:yields} {:layer 2} {:refines "AtomicAcquireProtected"} AcquireProtected({:linear "tid"} tid: X)
requires {:layer 1} tid != nil && InvLock(lock, b);
ensures {:layer 1} InvLock(lock, b);
{
  par Yield1() | Yield2();
  call Acquire(tid);
  par Yield1() | Yield2();
}

procedure {:left} {:layer 3} AtomicReleaseProtected({:linear "tid"} tid: X)
modifies lock;
{ assert tid != nil && lock == tid; lock := nil; }

procedure {:yields} {:layer 2} {:refines "AtomicReleaseProtected"} ReleaseProtected({:linear "tid"} tid: X)
requires {:layer 1} InvLock(lock, b);
ensures {:layer 1} InvLock(lock, b);
{
  par Yield1() | Yield2();
  call Release(tid);
  par Yield1() | Yield2();
}

procedure {:atomic} {:layer 2} AtomicAcquire({:linear "tid"} tid: X)
modifies lock;
{ assume lock == nil; lock := tid; }

procedure {:yields} {:layer 1} {:refines "AtomicAcquire"} Acquire({:linear "tid"} tid: X)
requires {:layer 1} tid != nil && InvLock(lock, b);
ensures {:layer 1} InvLock(lock, b);
{
    var status: bool;
    var tmp: X;

    call Yield1();
    
    while (true)
    invariant {:layer 1} InvLock(lock, b);
    {
        call status := CAS(tid, false, true);
        if (status) {
            call Yield1();
            return;
        }
        call Yield1();
    }
    yield;
}

procedure {:atomic} {:layer 2} AtomicRelease({:linear "tid"} tid: X)
modifies lock;
{ lock := nil; }

procedure {:yields} {:layer 1} {:refines "AtomicRelease"} Release({:linear "tid"} tid: X)
requires {:layer 1} InvLock(lock, b);
ensures {:layer 1} InvLock(lock, b);
{
    call Yield1();
    call CLEAR(tid, false);
    call Yield1();
}

procedure {:atomic} {:layer 1,2} AtomicTransferToGlobal({:linear "tid"} tid: X, {:linear_in "mem"} l: lmap)
modifies g;
{ g := l; }

procedure {:yields} {:layer 0} {:refines "AtomicTransferToGlobal"} TransferToGlobal({:linear "tid"} tid: X, {:linear_in "mem"} l: lmap);

procedure {:atomic} {:layer 1,2} AtomicTransferFromGlobal({:linear "tid"} tid: X) returns ({:linear "mem"} l: lmap)
modifies g;
{ l := g; g := emptyDom(g); }

procedure {:yields} {:layer 0} {:refines "AtomicTransferFromGlobal"} TransferFromGlobal({:linear "tid"} tid: X) returns ({:linear "mem"} l: lmap);

procedure {:both} {:layer 1,3} AtomicLoad({:linear "mem"} l: lmap, a: int) returns (v: int)
{ v := map(l)[a]; }

procedure {:yields} {:layer 0} {:refines "AtomicLoad"} Load({:linear "mem"} l: lmap, a: int) returns (v: int);

procedure {:both} {:layer 1,3} AtomicStore({:linear_in "mem"} l_in: lmap, a: int, v: int) returns ({:linear "mem"} l_out: lmap)
{ l_out := cons(dom(l_in), map(l_in)[a := v]); }

procedure {:yields} {:layer 0} {:refines "AtomicStore"} Store({:linear_in "mem"} l_in: lmap, a: int, v: int) returns ({:linear "mem"} l_out: lmap);

procedure {:atomic} {:layer 1} AtomicCAS(tid: X, prev: bool, next: bool) returns (status: bool)
modifies b, lock;
{
  if (*) {
    assume b == prev; b := next; status := true; lock := tid;
  } else {
    status := false;
  }
}

procedure {:yields} {:layer 0} {:refines "AtomicCAS"} CAS(tid: X, prev: bool, next: bool) returns (status: bool);

procedure {:atomic} {:layer 1} AtomicCLEAR(tid: X, next: bool)
modifies b, lock;
{ b := next; lock := nil; }

procedure {:yields} {:layer 0} {:refines "AtomicCLEAR"} CLEAR(tid: X, next: bool);
