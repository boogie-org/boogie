// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type X;
const nil: X;

type Y = int;

var {:layer 0,3} {:linear} g: Map (One int) int;
var {:layer 0,3} lock: X;
var {:layer 0,1} b: bool;

const p: int;

yield invariant {:layer 1} InvLock();
preserves lock != nil <==> b;

yield invariant {:layer 3} InvMem();
preserves Map_Contains(g, One(p)) && Map_Contains(g, One(p+4)) && Map_At(g, One(p)) == Map_At(g, One(p+4));

yield procedure {:layer 3} P({:linear} tid: One X)
requires {:layer 1,3} tid->val != nil;
preserves call InvLock();
preserves call InvMem();
{
    var t: int;
    var l: Map (One int) int;

    call AcquireProtected(tid);
    call l := TransferFromGlobalProtected(tid);
    call t := Load(l, p);
    call l := Store(l, p, t+1);
    call t := Load(l, p+4);
    call l := Store(l, p+4, t+1);
    call TransferToGlobalProtected(tid, l);
    call ReleaseProtected(tid);
}

both action {:layer 3} AtomicTransferToGlobalProtected({:linear} tid: One X, {:linear_in} l: Map (One int) int)
modifies g;
{ assert tid->val != nil && lock == tid->val; g := l; }

yield procedure {:layer 2}
TransferToGlobalProtected({:linear} tid: One X, {:linear_in} l: Map (One int) int)
refines AtomicTransferToGlobalProtected;
preserves call InvLock();
{
  call TransferToGlobal(tid, l);
}

both action {:layer 3} AtomicTransferFromGlobalProtected({:linear} tid: One X) returns ({:linear} l: Map (One int) int)
modifies g;
{ assert tid->val != nil && lock == tid->val; l := g; call g := Map_MakeEmpty(); }

yield procedure {:layer 2}
TransferFromGlobalProtected({:linear} tid: One X) returns ({:linear} l: Map (One int) int)
refines AtomicTransferFromGlobalProtected;
preserves call InvLock();
{
  call l := TransferFromGlobal(tid);
}

right action {:layer 3} AtomicAcquireProtected({:linear} tid: One X)
modifies lock;
{ assert tid->val != nil; assume lock == nil; lock := tid->val; }

yield procedure {:layer 2} AcquireProtected({:linear} tid: One X)
refines AtomicAcquireProtected;
requires {:layer 1} tid->val != nil;
preserves call InvLock();
{
  call Acquire(tid);
}

left action {:layer 3} AtomicReleaseProtected({:linear} tid: One X)
modifies lock;
{ assert tid->val != nil && lock == tid->val; lock := nil; }

yield procedure {:layer 2} ReleaseProtected({:linear} tid: One X)
refines AtomicReleaseProtected;
preserves call InvLock();
{
  call Release(tid);
}

atomic action {:layer 2} AtomicAcquire({:linear} tid: One X)
modifies lock;
{ assume lock == nil; lock := tid->val; }

yield procedure {:layer 1} Acquire({:linear} tid: One X)
refines AtomicAcquire;
requires {:layer 1} tid->val != nil;
preserves call InvLock();
{
    var status: bool;
    var tmp: X;

    while (true)
    invariant {:yields} true;
    invariant call InvLock();
    {
        call status := CAS(tid->val, false, true);
        if (status) {
            return;
        }
    }
}

atomic action {:layer 2} AtomicRelease({:linear} tid: One X)
modifies lock;
{ lock := nil; }

yield procedure {:layer 1} Release({:linear} tid: One X)
refines AtomicRelease;
preserves call InvLock();
{
  call CLEAR(tid->val, false);
}

atomic action {:layer 1,2} AtomicTransferToGlobal({:linear} tid: One X, {:linear_in} l: Map (One int) int)
modifies g;
{ g := l; }

yield procedure {:layer 0} TransferToGlobal({:linear} tid: One X, {:linear_in} l: Map (One int) int);
refines AtomicTransferToGlobal;

atomic action {:layer 1,2} AtomicTransferFromGlobal({:linear} tid: One X) returns ({:linear} l: Map (One int) int)
modifies g;
{ l := g; call g := Map_MakeEmpty(); }

yield procedure {:layer 0} TransferFromGlobal({:linear} tid: One X) returns ({:linear} l: Map (One int) int);
refines AtomicTransferFromGlobal;

both action {:layer 1,3} AtomicLoad({:linear} l: Map (One int) int, a: int) returns (v: int)
{ v := l->val[One(a)]; }

yield procedure {:layer 0} Load({:linear} l: Map (One int) int, a: int) returns (v: int);
refines AtomicLoad;

both action {:layer 1,3} AtomicStore({:linear_in} l_in: Map (One int) int, a: int, v: int)
  returns ({:linear} l_out: Map (One int) int)
{
  var one_a: One int;
  var _v: int;

  l_out := l_in;
  one_a := One(a);
  call _v := Map_Get(l_out, one_a);
  call Map_Put(l_out, one_a, v);
}

yield procedure {:layer 0} Store({:linear_in} l_in: Map (One int) int, a: int, v: int) returns ({:linear} l_out: Map (One int) int);
refines AtomicStore;

atomic action {:layer 1} AtomicCAS(tid: X, prev: bool, next: bool) returns (status: bool)
modifies b, lock;
{
  if (*) {
    assume b == prev; b := next; status := true; lock := tid;
  } else {
    status := false;
  }
}

yield procedure {:layer 0} CAS(tid: X, prev: bool, next: bool) returns (status: bool);
refines AtomicCAS;

atomic action {:layer 1} AtomicCLEAR(tid: X, next: bool)
modifies b, lock;
{ b := next; lock := nil; }

yield procedure {:layer 0} CLEAR(tid: X, next: bool);
refines AtomicCLEAR;
