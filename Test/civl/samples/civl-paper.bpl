// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type X;
const nil: X;

var {:layer 0,3} g: Lmap int int;
var {:layer 0,3} lock: X;
var {:layer 0,1} b: bool;

const p: int;

yield invariant {:layer 1} InvLock();
invariant lock != nil <==> b;

yield invariant {:layer 3} InvMem();
invariant g->dom[p] && g->dom[p+4] && g->val[p] == g->val[p+4];

yield procedure {:layer 3} P(tid: Lval X)
requires {:layer 1,3} tid->val != nil;
preserves call InvLock();
preserves call InvMem();
{
    var t: int;
    var l: Lmap int int;

    call AcquireProtected(tid);
    call l := TransferFromGlobalProtected(tid);
    call t := Load(l, p);
    call l := Store(l, p, t+1);
    call t := Load(l, p+4);
    call l := Store(l, p+4, t+1);
    call TransferToGlobalProtected(tid, l);
    call ReleaseProtected(tid);
}

both action {:layer 3} AtomicTransferToGlobalProtected(tid: Lval X, {:linear_in} l: Lmap int int)
modifies g;
{ assert tid->val != nil && lock == tid->val; g := l; }

yield procedure {:layer 2}
TransferToGlobalProtected(tid: Lval X, {:linear_in} l: Lmap int int)
refines AtomicTransferToGlobalProtected;
preserves call InvLock();
{
  call TransferToGlobal(tid, l);
}

both action {:layer 3} AtomicTransferFromGlobalProtected(tid: Lval X) returns (l: Lmap int int)
modifies g;
{ var t: Lset int; assert tid->val != nil && lock == tid->val; l := g; call t := Lset_Empty(); call g := Lmap_Alloc(t, g->val); }

yield procedure {:layer 2}
TransferFromGlobalProtected(tid: Lval X) returns (l: Lmap int int)
refines AtomicTransferFromGlobalProtected;
preserves call InvLock();
{
  call l := TransferFromGlobal(tid);
}

right action {:layer 3} AtomicAcquireProtected(tid: Lval X)
modifies lock;
{ assert tid->val != nil; assume lock == nil; lock := tid->val; }

yield procedure {:layer 2} AcquireProtected(tid: Lval X)
refines AtomicAcquireProtected;
requires {:layer 1} tid->val != nil;
preserves call InvLock();
{
  call Acquire(tid);
}

left action {:layer 3} AtomicReleaseProtected(tid: Lval X)
modifies lock;
{ assert tid->val != nil && lock == tid->val; lock := nil; }

yield procedure {:layer 2} ReleaseProtected(tid: Lval X)
refines AtomicReleaseProtected;
preserves call InvLock();
{
  call Release(tid);
}

atomic action {:layer 2} AtomicAcquire(tid: Lval X)
modifies lock;
{ assume lock == nil; lock := tid->val; }

yield procedure {:layer 1} Acquire(tid: Lval X)
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

atomic action {:layer 2} AtomicRelease(tid: Lval X)
modifies lock;
{ lock := nil; }

yield procedure {:layer 1} Release(tid: Lval X)
refines AtomicRelease;
preserves call InvLock();
{
  call CLEAR(tid->val, false);
}

atomic action {:layer 1,2} AtomicTransferToGlobal(tid: Lval X, {:linear_in} l: Lmap int int)
modifies g;
{ g := l; }

yield procedure {:layer 0} TransferToGlobal(tid: Lval X, {:linear_in} l: Lmap int int);
refines AtomicTransferToGlobal;

atomic action {:layer 1,2} AtomicTransferFromGlobal(tid: Lval X) returns (l: Lmap int int)
modifies g;
{ var t: Lset int; l := g; call t := Lset_Empty(); call g := Lmap_Alloc(t, g->val); }

yield procedure {:layer 0} TransferFromGlobal(tid: Lval X) returns (l: Lmap int int);
refines AtomicTransferFromGlobal;

both action {:layer 1,3} AtomicLoad(l: Lmap int int, a: int) returns (v: int)
{ v := l->val[a]; }

yield procedure {:layer 0} Load(l: Lmap int int, a: int) returns (v: int);
refines AtomicLoad;

both action {:layer 1,3} AtomicStore({:linear_in} l_in: Lmap int int, a: int, v: int) returns (l_out: Lmap int int)
{ l_out := l_in; l_out->val[a] := v; }

yield procedure {:layer 0} Store({:linear_in} l_in: Lmap int int, a: int, v: int) returns (l_out: Lmap int int);
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
