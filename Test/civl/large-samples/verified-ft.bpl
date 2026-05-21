/*

Copyright (c) 2017, Cormac Flanagan (University of California, Santa Cruz)
                    Stephen Freund (Williams College)
                    James Wilcox (University of Washington)

All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.

    * Redistributions in binary form must reproduce the above
      copyright notice, this list of conditions and the following
      disclaimer in the documentation and/or other materials provided
      with the distribution.

    * Neither the names of the University of California, Santa Cruz
      and Williams College nor the names of its contributors may be
      used to endorse or promote products derived from this software
      without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*/

/*
 * Proof of VerifiedFT correctness in Civl.
 */

// RUN: %parallel-boogie -timeLimit:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*
 * Tid
 */
type Tid = int;  // make int so you can iterate over Tids
const unique nil: Tid;

function {:inline} ValidTid(tid : Tid): bool {
  tid != nil && tid >= 0
}

/*
 * datatype Epoch = Tid*Clock
 */
datatype Epoch { epoch(tid:Tid, clock:int) }

const unique SHARED: Epoch;

function {:inline} EpochInc(e : Epoch): Epoch {
  epoch(e->tid, e->clock + 1)
}

function {:inline} EpochIsShared(e : Epoch): bool {
  e == SHARED
}

function {:inline} EpochLeq(e1 : Epoch, e2 : Epoch): bool {
  e1->tid == e2->tid && e1->clock <=  e2->clock
}

function {:inline} max(a : int, b : int) : int {
  if (a < b) then b else a
}

function {:inline} EpochMax(e1 : Epoch, e2 : Epoch): Epoch {
  epoch(e1->tid, max(e1->clock, e2->clock))
}

function {:inline} EpochInit(tid: Tid): Epoch {
  epoch(tid, 0)
}


/*
 * VC
 */
type VC = [Tid]Epoch;

// primitive accessors to array
// len of VC is stored at -1.
function {:inline} VCArrayLen(vc: VC): int { vc[-1]->clock }
function {:inline} VCArraySetLen(vc: VC, n: int): VC { vc[-1 := epoch(-1,n)] }
function {:inline} VCArrayGet(vc: VC, i: int): Epoch { vc[i] }


/*
 * Shadow State
 */
type Lock;
type Var;

/*
 * datatype Shadowable = tid | lock | var
 */
datatype Shadowable {
  ShadowableTid(tid: Tid),
  ShadowableLock(l: Lock),
  ShadowableVar(x: Var)
}

var {:layer 0,30} shadow.VC   : [Shadowable] VC;
var {:layer 0,30} shadow.Lock : [Shadowable] Tid;
var {:layer 0,30} sx.W        : [Var]Epoch;
var {:layer 0,30} sx.R        : [Var]Epoch;

/*
 * Trace Invariant Support
 */
type ThreadStatus = int;
function{:inline} UNUSED(): ThreadStatus { 0 }
function{:inline} NEW(): ThreadStatus { 1 }
function{:inline} RUNNING(): ThreadStatus { 2 }
function{:inline} STOPPED(): ThreadStatus { 3 }

var {:layer 0,30} thread.State:     [Tid]ThreadStatus;  // status of each thread
var {:layer 0,30} thread.ForkedBy:  [Tid]Tid;           // if forkedBy[t] = u, the u started t
var {:layer 0,30} thread.HasJoined: [Tid,Tid]bool;      // if hasJoined[t,u], then t joined u.


/*
 * Needed for [Read Share]
 */
const unique EMPTY_MAP: [Tid]Epoch;
axiom (forall i : Tid :: EMPTY_MAP[i] == EpochInit(i));

function {:inline} VC.bottom(): VC { VCArraySetLen(EMPTY_MAP,0) }


/*
 * State Invariants
 */
function {:inline false} VarsRepOk(w: [Var]Epoch, r: [Var]Epoch ): bool {
  (forall v: Var :: ValidTid(w[v]->tid)) &&
  (forall v: Var :: r[v] == SHARED || (r[v]->tid >= 0 && r[v]->tid != nil))
}

function {:inline false} VCRepOk(vc: VC): bool {
  VCArrayLen(vc) >= 0 &&
  (forall j: int :: {vc[j]} 0 <= j && j < VCArrayLen(vc) ==> vc[j]->clock >= 0) &&
  (forall j: int :: {vc[j]} 0 <= j && j < VCArrayLen(vc) ==> vc[j]->tid == j) &&
  (forall j: int :: VCArrayLen(vc) <= j ==> vc[j] == EpochInit(j))
}

function {:inline} VCsRepOk(vcs: [Shadowable]VC): bool {
  (forall s : Shadowable :: VCRepOk(vcs[s]))
}

function {:inline} FTRepOk(vcs: [Shadowable]VC, w: [Var]Epoch, r: [Var]Epoch): bool {
  VCsRepOk(vcs) &&
  VarsRepOk(w, r)
}


/*
 * Environment Assumptions -- what's preserved across yields
 */
function {:inline} LocksPreserved(tid: Tid, oldLocks: [Shadowable] Tid, locks: [Shadowable]Tid): bool {
  (forall v: Shadowable :: oldLocks[v] == tid ==> locks[v] == tid)
}

function {:inline} SharedInvPreserved(oldR: [Var] Epoch, r: [Var] Epoch): bool {
  (forall x: Var :: oldR[x] == SHARED ==> r[x] == SHARED)
}

function {:inline} FTPreserved(tid: Tid,
                               oldLocks: [Shadowable] Tid, oldVcs: [Shadowable]VC, oldW: [Var]Epoch, oldR: [Var]Epoch,
                                  locks: [Shadowable] Tid,    vcs: [Shadowable]VC,    w: [Var]Epoch,    r: [Var]Epoch): bool {
  LocksPreserved(tid, oldLocks, locks) &&
  SharedInvPreserved(oldR, r) &&
  (forall s: Shadowable :: oldLocks[s] == tid ==> vcs[s] == oldVcs[s]) &&
  (forall x: Var :: oldLocks[ShadowableVar(x)] == tid ==> r[x] == oldR[x]) &&
  (forall x: Var :: oldLocks[ShadowableVar(x)] == tid ==> w[x] == oldW[x])
}

/****** Layer 0  ******/

// VarState Lock
yield procedure {:layer 0} AcquireVarLock({:linear} tid: One Tid, x : Var);
refines AtomicAcquireVarLock;
right action {:layer 1,20} AtomicAcquireVarLock({:linear} tid: One Tid, x : Var)
modifies shadow.Lock;
{ assert ValidTid(tid->val); assume shadow.Lock[ShadowableVar(x)] == nil; shadow.Lock[ShadowableVar(x)] := tid->val; }

yield procedure {:layer 0} ReleaseVarLock({:linear} tid: One Tid, x : Var);
refines AtomicReleaseVarLock;
left action {:layer 1,20} AtomicReleaseVarLock({:linear} tid: One Tid, x : Var)
modifies shadow.Lock;
{ assert ValidTid(tid->val); assert shadow.Lock[ShadowableVar(x)] == tid->val; shadow.Lock[ShadowableVar(x)] := nil; }


// ThreadState
yield procedure {:layer 0} ThreadStateGetE({:linear} tid: One Tid) returns (e:Epoch);
refines AtomicThreadStateGetE;
both action {:layer 1,20} AtomicThreadStateGetE({:linear} tid: One Tid) returns (e:Epoch)
{ assert ValidTid(tid->val); assert shadow.Lock[ShadowableTid(tid->val)] == tid->val; e := shadow.VC[ShadowableTid(tid->val)][tid->val]; }


// VarState
yield procedure {:layer 0} VarStateSetW({:linear} tid: One Tid, x : Var, e:Epoch);
refines AtomicVarStateSetW;
atomic action {:layer 1,20} AtomicVarStateSetW({:linear} tid: One Tid, x : Var, e:Epoch)
modifies sx.W;
{ assert ValidTid(tid->val); assert shadow.Lock[ShadowableVar(x)] == tid->val; sx.W[x] := e; }

yield procedure {:layer 0} VarStateGetW({:linear} tid: One Tid, x : Var) returns (e:Epoch);
refines AtomicVarStateGetW;
both action {:layer 1,20} AtomicVarStateGetW({:linear} tid: One Tid, x : Var) returns (e:Epoch)
{ assert ValidTid(tid->val); assert shadow.Lock[ShadowableVar(x)] == tid->val; e := sx.W[x]; }

yield procedure {:layer 0} VarStateGetWNoLock({:linear} tid: One Tid, x : Var) returns (e:Epoch);
refines AtomicVarStateGetWNoLock;
atomic action {:layer 1,20} AtomicVarStateGetWNoLock({:linear} tid: One Tid, x : Var) returns (e:Epoch)
{ assert ValidTid(tid->val); e := sx.W[x]; }

yield procedure {:layer 0} VarStateSetR({:linear} tid: One Tid, x : Var, e:Epoch);
refines AtomicVarStateSetR;
atomic action {:layer 1,20} AtomicVarStateSetR({:linear} tid: One Tid, x : Var, e:Epoch)
modifies sx.R;
{ assert ValidTid(tid->val); assert shadow.Lock[ShadowableVar(x)] == tid->val; assert sx.R[x] != SHARED; sx.R[x] := e; }

yield procedure {:layer 0} VarStateGetRNoLock({:linear} tid: One Tid, x : Var) returns (e:Epoch);
refines AtomicVarStateGetRNoLock;
atomic action {:layer 1,20} AtomicVarStateGetRNoLock({:linear} tid: One Tid, x : Var) returns (e:Epoch)
{ assert ValidTid(tid->val); e := sx.R[x]; }

yield procedure {:layer 0} VarStateGetR({:linear} tid: One Tid, x : Var) returns (e:Epoch);
refines AtomicVarStateGetR;
both action {:layer 1,20} AtomicVarStateGetR({:linear} tid: One Tid, x : Var) returns (e:Epoch)
{ assert ValidTid(tid->val); assert shadow.Lock[ShadowableVar(x)] == tid->val; e := sx.R[x]; }

yield procedure {:layer 0} VarStateGetRShared({:linear} tid: One Tid, x : Var) returns (e:Epoch);
refines AtomicVarStateGetRShared;
right action {:layer 1,20} AtomicVarStateGetRShared({:linear} tid: One Tid, x : Var) returns (e:Epoch)
{ assert ValidTid(tid->val); assume sx.R[x] == SHARED; e := SHARED; }


// VCs

yield procedure {:layer 0} VCGetSize({:linear} tid: One Tid, r: Shadowable) returns (i: int);
refines AtomicVCGetSize;
both action {:layer 1,10} AtomicVCGetSize({:linear} tid: One Tid, r: Shadowable) returns (i: int)
{
   assert ValidTid(tid->val);
   assert (shadow.Lock[r] == tid->val);
   i := VCArrayLen(shadow.VC[r]);
}

yield procedure {:layer 0} VCGetElem({:linear} tid: One Tid, r: Shadowable, i: int) returns (e: Epoch);
refines AtomicVCGetElem;
both action {:layer 1,20} AtomicVCGetElem({:linear} tid: One Tid, r: Shadowable, i: int) returns (e: Epoch)
{
   assert ValidTid(tid->val);
   assert (shadow.Lock[r] == tid->val);
   e := VCArrayGet(shadow.VC[r], i);
}

yield procedure {:layer 0} VCGetElemShared({:linear} tid: One Tid, x : Var) returns (e: Epoch);
refines AtomicVCGetElemShared;
atomic action {:layer 1,20} AtomicVCGetElemShared({:linear} tid: One Tid, x : Var) returns (e: Epoch)
{
   assert sx.R[x] == SHARED;
   assert ValidTid(tid->val);
   e := VCArrayGet(shadow.VC[ShadowableVar(x)], tid->val);
}

yield procedure {:layer 0} VCSetElemShared({:linear} tid: One Tid, x : Var, e: Epoch);
refines AtomicVCSetElemShared;
both action {:layer 1,20} AtomicVCSetElemShared({:linear} tid: One Tid, x : Var, e: Epoch)
modifies shadow.VC;
{
   assert sx.R[x] == SHARED;
   assert ValidTid(tid->val);
   assert (shadow.Lock[ShadowableVar(x)] == tid->val);
   shadow.VC[ShadowableVar(x)][tid->val] := e;
   shadow.VC[ShadowableVar(x)] := VCArraySetLen(shadow.VC[ShadowableVar(x)], max(VCArrayLen(shadow.VC[ShadowableVar(x)]),tid->val + 1));
}

yield procedure {:layer 0} VCSetElem({:linear} tid: One Tid, r: Shadowable, i: int, e: Epoch);
refines AtomicVCSetElem;
both action {:layer 1,20} AtomicVCSetElem({:linear} tid: One Tid, r: Shadowable, i: int, e: Epoch)
modifies shadow.VC;
{
   assert r is ShadowableVar ==> sx.R[r->x] != SHARED;
   assert ValidTid(tid->val);
   assert (shadow.Lock[r] == tid->val);
   shadow.VC[r][i] := e;
   shadow.VC[r] := VCArraySetLen(shadow.VC[r], max(VCArrayLen(shadow.VC[r]),i+1));
}

yield procedure {:layer 0} VCInit({:linear} tid: One Tid, r: Shadowable);
refines AtomicVCInit;
both action {:layer 1,20} AtomicVCInit({:linear} tid: One Tid, r: Shadowable)
modifies shadow.VC;
{
   assert ValidTid(tid->val);
   assert r is ShadowableVar ==> sx.R[r->x] != SHARED;
   assert (shadow.Lock[r] == tid->val);
   shadow.VC[r] := VC.bottom();
}

/****** Layer 10 -> 20 ******/

yield invariant {:layer 10} Yield_FTRepOk_10();
preserves FTRepOk(shadow.VC, sx.W, sx.R);

yield invariant {:layer 10} Yield_Lock_10({:linear} tid: One Tid, v: Shadowable);
preserves ValidTid(tid->val);
preserves shadow.Lock[v] == tid->val;

yield invariant {:layer 10} Yield_FTPreserved_10({:linear} tid: One Tid, old.shadow.Lock: [Shadowable]Tid, old.shadow.VC: [Shadowable]VC, old.sx.W: [Var]Epoch, old.sx.R: [Var]Epoch);
preserves ValidTid(tid->val);
preserves FTPreserved(tid->val, old.shadow.Lock, old.shadow.VC, old.sx.W, old.sx.R, shadow.Lock, shadow.VC, sx.W, sx.R);

yield invariant {:layer 10} Yield_VCPreserved_10({:linear} tid: One Tid, v1: Shadowable, v2: Shadowable, old.shadow.Lock: [Shadowable]Tid, old.shadow.VC: [Shadowable]VC);
preserves ValidTid(tid->val);
preserves LocksPreserved(tid->val, old.shadow.Lock, shadow.Lock);
preserves (forall s: Shadowable :: s != v1 && s != v2 && old.shadow.Lock[s] == tid->val ==> old.shadow.VC[s] == shadow.VC[s]);

both action {:layer 11,20} AtomicVC.Leq({:linear} tid: One Tid, v1: Shadowable, v2: Shadowable) returns (res: bool)
{
   assert ValidTid(tid->val);
   assert shadow.Lock[v1] == tid->val;
   assert shadow.Lock[v2] == tid->val;
   assert shadow.Lock[ShadowableTid(tid->val)] == tid->val;
   assert v1 is ShadowableVar ==> sx.R[v1->x] == SHARED;
   assert !(v2 is ShadowableVar);
   res := (forall j : int :: 0 <= j ==> EpochLeq(VCArrayGet(shadow.VC[v1], j), VCArrayGet(shadow.VC[v2], j)));
}

yield procedure {:layer 10}
VC.Leq({:linear} tid: One Tid, v1: Shadowable, v2: Shadowable) returns (res: bool)
refines AtomicVC.Leq;
preserves call Yield_FTRepOk_10();
preserves call Yield_FTPreserved_10(tid, old(shadow.Lock), old(shadow.VC), old(sx.W), old(sx.R));
{
  var vc1, vc2: VC;
  var len1, len2 : int;
  var e1, e2: Epoch;
  var i: int;

  call len1 := VCGetSize(tid, v1);
  call len2 := VCGetSize(tid, v1);

  i := 0;
  while (i < max(len1, len2))
    invariant {:layer 10} 0 <= i;
    invariant {:layer 10} (forall j : int ::
         0 <= j && j < i ==>
         EpochLeq(VCArrayGet(shadow.VC[v1], j), VCArrayGet(shadow.VC[v2], j)));
  {
    call e1 := VCGetElem(tid, v1, i);
    call e2 := VCGetElem(tid, v2, i);
    if (!EpochLeq(e1, e2)) {
      res := false;
      return;
    }

    i := i + 1;
  }

  res := true;
  return;
}

both action {:layer 11,20} AtomicVC.Copy({:linear} tid: One Tid, v1: Shadowable, v2: Shadowable)
modifies shadow.VC;
{
    var {:pool "A"} vc: VC;
    assert ValidTid(tid->val);
    assert v1 != v2;
    assert shadow.Lock[ShadowableTid(tid->val)] == tid->val;
    assert shadow.Lock[v1] == tid->val;
    assert shadow.Lock[v2] == tid->val;
    assert !(v1 is ShadowableVar);
    assert !(v2 is ShadowableVar);
    assert VCRepOk(shadow.VC[v2]);
    assert VCRepOk(shadow.VC[v1]);
    if (*) {
        assume VCRepOk(vc);
        assume VCArrayLen(vc) == max(VCArrayLen(shadow.VC[v1]),VCArrayLen(shadow.VC[v2]));
        assume (forall j: int :: 0 <= j ==> VCArrayGet(vc, j) == VCArrayGet(shadow.VC[v2], j));
        shadow.VC[v1] := vc;
    } else {
        shadow.VC[v1] := shadow.VC[v2];
    }
}

yield procedure {:layer 10}
VC.Copy({:linear} tid: One Tid, v1: Shadowable, v2: Shadowable)
refines AtomicVC.Copy;
preserves call Yield_FTRepOk_10();
requires call Yield_FTPreserved_10(tid, old(shadow.Lock), old(shadow.VC), old(sx.W), old(sx.R));
ensures call Yield_VCPreserved_10(tid, v1, v1, old(shadow.Lock), old(shadow.VC));
{
  var len1, len2 : int;
  var e1, e2: Epoch;
  var i: int;

  var {:layer 10} oldVC : [Shadowable] [Tid]Epoch;
  var {:layer 10} oldLock : [Shadowable] Tid;

  call {:layer 10} oldLock := Copy(shadow.Lock);
  call {:layer 10} oldVC := Copy(shadow.VC);

  call len1 := VCGetSize(tid, v1);
  call len2 := VCGetSize(tid, v2);

  i := 0;
  while (i < max(len1, len2))
    invariant {:layer 10} (forall s: Shadowable :: s != v1 ==> shadow.VC[s] == oldVC[s]);
    invariant {:layer 10} (forall s: Shadowable :: oldLock[s] == tid->val ==> shadow.Lock[s] == tid->val);
    invariant {:layer 10} VCRepOk(shadow.VC[v1]);
    invariant {:layer 10} i >= 0;
    invariant {:layer 10} i <= max(len1, len2);
    invariant {:layer 10} VCArrayLen(shadow.VC[v1]) == max(len1, i);
    invariant {:layer 10} (forall j : int :: 0 <= j && j < i      ==> VCArrayGet(shadow.VC[v1], j) == VCArrayGet(shadow.VC[v2], j));
    invariant {:layer 10} (forall j : int :: max(len1, len2) <=j  ==> VCArrayGet(shadow.VC[v1], j) == VCArrayGet(shadow.VC[v2], j));
  {
    call e2 := VCGetElem(tid, v2, i);
    call VCSetElem(tid, v1, i, e2);
    i := i + 1;
  }
  assume {:add_to_pool "A", shadow.VC[v1]} true;
}


right action {:layer 11,20} AtomicVC.Join({:linear} tid: One Tid, v1: Shadowable, v2: Shadowable)
modifies shadow.VC;
{
    var {:pool "A"} vc: VC;
    assert ValidTid(tid->val);
    assert v1 != v2;
    assert shadow.Lock[ShadowableTid(tid->val)] == tid->val;
    assert shadow.Lock[v1] == tid->val;
    assert shadow.Lock[v2] == tid->val;
    assert !(v1 is ShadowableVar);
    assert !(v2 is ShadowableVar);
    assert VCRepOk(shadow.VC[v2]);
    assume VCRepOk(vc);
    assume VCArrayLen(vc) == max(VCArrayLen(shadow.VC[v1]),VCArrayLen(shadow.VC[v2]));
    assume (forall j: int :: 0 <= j ==> VCArrayGet(vc, j) == EpochMax(VCArrayGet(shadow.VC[v1], j), VCArrayGet(shadow.VC[v2], j)));
    shadow.VC[v1] := vc;
}

yield procedure {:layer 10}
VC.Join({:linear} tid: One Tid, v1: Shadowable, v2: Shadowable)
refines AtomicVC.Join;
preserves call Yield_FTRepOk_10();
requires call Yield_FTPreserved_10(tid, old(shadow.Lock), old(shadow.VC), old(sx.W), old(sx.R));
ensures call Yield_VCPreserved_10(tid, v1, v1, old(shadow.Lock), old(shadow.VC));
{
  var len1, len2 : int;
  var e1, e2: Epoch;
  var i: int;

  var {:layer 10} oldVC : [Shadowable] [Tid]Epoch;
  var {:layer 10} oldLock : [Shadowable] Tid;

  call {:layer 10} oldLock := Copy(shadow.Lock);
  call {:layer 10} oldVC := Copy(shadow.VC);

  call len1 := VCGetSize(tid, v1);
  call len2 := VCGetSize(tid, v2);

  i := 0;
  while (i < max(len1, len2))
    invariant {:layer 10} (forall s: Shadowable :: s != v1 ==> shadow.VC[s] == oldVC[s]);
    invariant {:layer 10} (forall s: Shadowable :: oldLock[s] == tid->val ==> shadow.Lock[s] == tid->val);
    invariant {:layer 10} VCRepOk(shadow.VC[v1]);
    invariant {:layer 10} i >= 0;
    invariant {:layer 10} i <= max(len1, len2);
    invariant {:layer 10} VCArrayLen(shadow.VC[v1]) == max(len1, i);
    invariant {:layer 10} (forall j : int :: 0 <= j && i <= j ==> VCArrayGet(shadow.VC[v1], j) == VCArrayGet(oldVC[v1], j));
    invariant {:layer 10} (forall j : int :: 0 <= j && j < i  ==> VCArrayGet(shadow.VC[v1], j) == EpochMax(VCArrayGet(oldVC[v1], j), VCArrayGet(shadow.VC[v2], j)));
  {
    call e1 := VCGetElem(tid, v1, i);
    call e2 := VCGetElem(tid, v2, i);
    call VCSetElem(tid, v1, i, EpochMax(e1, e2));
    i := i + 1;
  }
  assume {:add_to_pool "A", shadow.VC[v1]} true;
}

both action {:layer 11,20} AtomicVC.Inc({:linear} tid: One Tid, v: Shadowable, i: int)
modifies shadow.VC;
{
   assert ValidTid(tid->val);
   assert shadow.Lock[ShadowableTid(tid->val)] == tid->val;
   assert shadow.Lock[v] == tid->val;
   assert !(v is ShadowableVar);
   assert i >= 0;
   assert VCRepOk(shadow.VC[v]);
   shadow.VC[v] := VCArraySetLen(shadow.VC[v], max(VCArrayLen(shadow.VC[v]), i+1));
   shadow.VC[v] := shadow.VC[v][i := EpochInc(shadow.VC[v][i])];
}

yield procedure {:layer 10}
VC.Inc({:linear} tid: One Tid, v: Shadowable, i: int)
refines AtomicVC.Inc;
preserves call Yield_FTRepOk_10();
requires call Yield_FTPreserved_10(tid, old(shadow.Lock), old(shadow.VC), old(sx.W), old(sx.R));
ensures call Yield_VCPreserved_10(tid, v, v, old(shadow.Lock), old(shadow.VC));
{
  var e: Epoch;

  call e := VCGetElem(tid, v, i);
  call VCSetElem(tid, v, i, EpochInc(e));
}



/****** Layer 20 --> 30 ******/

yield invariant {:layer 20} Yield_FTRepOk_20();
preserves FTRepOk(shadow.VC, sx.W, sx.R);

yield invariant {:layer 20} Yield_Lock_20({:linear} tid: One Tid, v: Shadowable);
preserves ValidTid(tid->val);
preserves shadow.Lock[v] == tid->val;

yield invariant {:layer 20} Yield_VCPreserved_20({:linear} tid: One Tid, v1: Shadowable, v2: Shadowable, old.shadow.Lock: [Shadowable]Tid, old.shadow.VC: [Shadowable]VC);
preserves ValidTid(tid->val);
preserves LocksPreserved(tid->val, old.shadow.Lock, shadow.Lock);
preserves (forall s: Shadowable :: s != v1 && s != v2 && old.shadow.Lock[s] == tid->val ==> old.shadow.VC[s] == shadow.VC[s]);

yield invariant {:layer 20} Yield_FTPreserved_20({:linear} tid: One Tid, old.shadow.Lock: [Shadowable]Tid, old.shadow.VC: [Shadowable]VC, old.sx.W: [Var]Epoch, old.sx.R: [Var]Epoch);
preserves ValidTid(tid->val);
preserves FTPreserved(tid->val, old.shadow.Lock, old.shadow.VC, old.sx.W, old.sx.R, shadow.Lock, shadow.VC, sx.W, sx.R);

atomic action {:layer 21,30} AtomicFork({:linear} tid: One Tid, uid : Tid)
modifies shadow.VC;
{
    var v1,v2: Shadowable;
    var {:pool "A"} vc1, vc2: VC;

    assert ValidTid(tid->val);
    assert ValidTid(uid);
    assert shadow.Lock[ShadowableTid(tid->val)] == tid->val;
    assert shadow.Lock[ShadowableTid(uid)] == tid->val;
    assert tid->val != uid;

    v1 := ShadowableTid(uid);
    v2 := ShadowableTid(tid->val);

    assume VCArrayLen(vc1) == max(VCArrayLen(shadow.VC[v1]),VCArrayLen(shadow.VC[v2]));
    assume VCRepOk(vc1);
    assume (forall j: int :: 0 <= j ==> VCArrayGet(vc1, j) == EpochMax(VCArrayGet(shadow.VC[v1], j), VCArrayGet(shadow.VC[v2], j)));

    assume VCRepOk(vc2);
    assume VCArrayLen(vc2) == max(VCArrayLen(vc2), tid->val + 1);
    assume (forall j: int :: 0 <= j && j != tid->val ==> VCArrayGet(vc2, j) == VCArrayGet(shadow.VC[v2], j));
    assume VCArrayGet(vc2, tid->val) == EpochInc(VCArrayGet(shadow.VC[v2], tid->val));

    shadow.VC[v1] := vc1;
    shadow.VC[v2] := vc2;
}

yield procedure {:layer 20} Fork({:linear} tid: One Tid, uid : Tid)
refines AtomicFork;
preserves call Yield_FTRepOk_10();
requires call Yield_FTPreserved_10(tid, old(shadow.Lock), old(shadow.VC), old(sx.W), old(sx.R));
ensures call Yield_VCPreserved_10(tid, ShadowableTid(tid->val), ShadowableTid(uid), old(shadow.Lock), old(shadow.VC));
preserves call Yield_FTRepOk_20();
requires call Yield_FTPreserved_20(tid, old(shadow.Lock), old(shadow.VC), old(sx.W), old(sx.R));
ensures call Yield_VCPreserved_20(tid, ShadowableTid(tid->val), ShadowableTid(uid), old(shadow.Lock), old(shadow.VC));
{
  call VC.Join(tid, ShadowableTid(uid), ShadowableTid(tid->val));
  call VC.Inc(tid, ShadowableTid(tid->val), tid->val);
  assume {:add_to_pool "A", shadow.VC[ShadowableTid(uid)], shadow.VC[ShadowableTid(tid->val)]} true;
}

atomic action {:layer 21,30} AtomicJoin({:linear} tid: One Tid, uid : Tid)
modifies shadow.VC;
{
    var v1, v2: Shadowable;
    var vc: VC;

    assert ValidTid(tid->val);
    assert ValidTid(uid);
    assert shadow.Lock[ShadowableTid(tid->val)] == tid->val;
    assert shadow.Lock[ShadowableTid(uid)] == tid->val;
    assert tid->val != uid;

    v1 := ShadowableTid(uid);
    v2 := ShadowableTid(tid->val);

    assume VCArrayLen(vc) == max(VCArrayLen(shadow.VC[v1]),VCArrayLen(shadow.VC[v2]));
    assume VCRepOk(vc);
    assume (forall j: int :: 0 <= j ==>
        VCArrayGet(vc, j) ==
        EpochMax(VCArrayGet(shadow.VC[v2], j), VCArrayGet(shadow.VC[v1], j)));
    shadow.VC[v2] := vc;
}

yield procedure {:layer 20}
Join({:linear} tid: One Tid, uid : Tid)
refines AtomicJoin;
preserves call Yield_FTRepOk_10();
requires call Yield_FTPreserved_10(tid, old(shadow.Lock), old(shadow.VC), old(sx.W), old(sx.R));
ensures call Yield_VCPreserved_10(tid, ShadowableTid(tid->val), ShadowableTid(tid->val), old(shadow.Lock), old(shadow.VC));
preserves call Yield_FTRepOk_20();
requires call Yield_FTPreserved_20(tid, old(shadow.Lock), old(shadow.VC), old(sx.W), old(sx.R));
ensures call Yield_VCPreserved_20(tid, ShadowableTid(tid->val), ShadowableTid(tid->val), old(shadow.Lock), old(shadow.VC));
{
  call VC.Join(tid, ShadowableTid(tid->val), ShadowableTid(uid));
}


atomic action {:layer 21,30} AtomicAcquire({:linear} tid: One Tid, l: Lock)
modifies shadow.VC;
{
    var v1, v2: Shadowable;
    var vc: VC;

    assert ValidTid(tid->val);
    assert shadow.Lock[ShadowableLock(l)] == tid->val;
    assert shadow.Lock[ShadowableTid(tid->val)] == tid->val;

    v1 := ShadowableTid(tid->val);
    v2 := ShadowableLock(l);
    assume VCRepOk(vc);
    assume VCArrayLen(vc) == max(VCArrayLen(shadow.VC[v1]),VCArrayLen(shadow.VC[v2]));
    assume (forall j: int :: 0 <= j ==>
        VCArrayGet(vc, j) ==
        EpochMax(VCArrayGet(shadow.VC[v1], j), VCArrayGet(shadow.VC[v2], j)));
    shadow.VC[v1] := vc;
}

yield procedure {:layer 20} Acquire({:linear} tid: One Tid, l: Lock)
refines AtomicAcquire;
preserves call Yield_FTRepOk_10();
requires call Yield_FTPreserved_10(tid, old(shadow.Lock), old(shadow.VC), old(sx.W), old(sx.R));
ensures call Yield_VCPreserved_10(tid, ShadowableTid(tid->val), ShadowableTid(tid->val), old(shadow.Lock), old(shadow.VC));
preserves call Yield_FTRepOk_20();
requires call Yield_FTPreserved_20(tid, old(shadow.Lock), old(shadow.VC), old(sx.W), old(sx.R));
ensures call Yield_VCPreserved_20(tid, ShadowableTid(tid->val), ShadowableTid(tid->val), old(shadow.Lock), old(shadow.VC));
{
  call VC.Join(tid, ShadowableTid(tid->val), ShadowableLock(l));
}

atomic action {:layer 21,30} AtomicRelease({:linear} tid: One Tid, l: Lock)
modifies shadow.VC;
{
    var v1,v2: Shadowable;
    var {:pool "A"} vc1, vc2: VC;

    assert ValidTid(tid->val);
    assert shadow.Lock[ShadowableTid(tid->val)] == tid->val;
    assert shadow.Lock[ShadowableLock(l)] == tid->val;

    v1 := ShadowableLock(l);
    v2 := ShadowableTid(tid->val);

    // Use the same strategy as in Copy's atomic spec.
    if (*) {
        assume VCRepOk(vc1);
        assume VCArrayLen(vc1) == max(VCArrayLen(shadow.VC[v1]),VCArrayLen(shadow.VC[v2]));
        assume (forall j: int :: 0 <= j ==> VCArrayGet(vc1, j) == VCArrayGet(shadow.VC[v2], j));
    } else {
        assume vc1 == shadow.VC[v2];
    }

    assume VCRepOk(vc2);
    assume VCArrayLen(vc2) == max(VCArrayLen(vc2), tid->val + 1);
    assume (forall j: int :: 0 <= j && j != tid->val ==> VCArrayGet(vc2, j) == VCArrayGet(shadow.VC[v2], j));
    assume VCArrayGet(vc2, tid->val) == EpochInc(VCArrayGet(shadow.VC[v2], tid->val));

    shadow.VC[v1] := vc1;
    shadow.VC[v2] := vc2;
}

yield procedure {:layer 20} Release({:linear} tid: One Tid, l: Lock)
refines AtomicRelease;
preserves call Yield_FTRepOk_10();
requires call Yield_FTPreserved_10(tid, old(shadow.Lock), old(shadow.VC), old(sx.W), old(sx.R));
ensures call Yield_VCPreserved_10(tid, ShadowableTid(tid->val), ShadowableLock(l), old(shadow.Lock), old(shadow.VC));
preserves call Yield_FTRepOk_20();
requires call Yield_FTPreserved_20(tid, old(shadow.Lock), old(shadow.VC), old(sx.W), old(sx.R));
ensures call Yield_VCPreserved_20(tid, ShadowableTid(tid->val), ShadowableLock(l), old(shadow.Lock), old(shadow.VC));
{
  var sm : Shadowable;
  var st : Shadowable;

  call VC.Copy(tid, ShadowableLock(l), ShadowableTid(tid->val));
  call VC.Inc(tid, ShadowableTid(tid->val), tid->val);
  assume {:add_to_pool "A", shadow.VC[ShadowableLock(l)], shadow.VC[ShadowableTid(tid->val)]} true;
}


atomic action {:layer 21,30} AtomicWrite({:linear} tid: One Tid, x : Var) returns (ok : bool)
modifies sx.W;
{
             var st : Shadowable;
             var sx : Shadowable;

             assert ValidTid(tid->val);
             st := ShadowableTid(tid->val);
             sx := ShadowableVar(x);
             goto WriteFastPath, WriteExclusive, WritedShared, WriteWriteRace, ReadWriteRace, SharedWriteRace;
          WriteFastPath:
             ok := true;
             assume sx.W[x] == VCArrayGet(shadow.VC[st], tid->val);
             return;
          WriteExclusive:
             ok := true;
             assume EpochLeq(sx.W[x], VCArrayGet(shadow.VC[st], sx.W[x]->tid));
             assume sx.R[x] != SHARED;
             assume EpochLeq(sx.R[x], VCArrayGet(shadow.VC[st], sx.R[x]->tid));
             sx.W[x] := VCArrayGet(shadow.VC[st], tid->val);
             return;
          WritedShared:
             ok := true;
             assume EpochLeq(sx.W[x], VCArrayGet(shadow.VC[st], sx.W[x]->tid));
             assume sx.R[x] == SHARED;
             assume (forall j : int ::
                      0 <= j && j < max(VCArrayLen(shadow.VC[sx]), VCArrayLen(shadow.VC[st])) ==>
                      EpochLeq(VCArrayGet(shadow.VC[sx], j), VCArrayGet(shadow.VC[st], j)));
             sx.W[x] := VCArrayGet(shadow.VC[st], tid->val);
             return;
          WriteWriteRace:
             ok := false;
             assume !EpochLeq(sx.W[x], VCArrayGet(shadow.VC[st], sx.W[x]->tid));
             return;
          ReadWriteRace:
             ok := false;
             assume sx.R[x] != SHARED;
             assume !EpochLeq(sx.R[x], VCArrayGet(shadow.VC[st], sx.R[x]->tid));
             return;
          SharedWriteRace:
             ok := false;
             assume sx.R[x] == SHARED;
             assume !(forall j : int ::
                      0 <= j && j < max(VCArrayLen(shadow.VC[st]),VCArrayLen(shadow.VC[sx])) ==>
                      EpochLeq(VCArrayGet(shadow.VC[sx], j), VCArrayGet(shadow.VC[st], j)));
             return;
}

yield procedure {:layer 20} Write({:linear} tid: One Tid, x : Var) returns (ok : bool)
refines AtomicWrite;
preserves call Yield_FTRepOk_10();
preserves call Yield_FTPreserved_10(tid, old(shadow.Lock), old(shadow.VC), old(sx.W), old(sx.R));
preserves call Yield_FTRepOk_20();
requires call Yield_Lock_20(tid, ShadowableTid(tid->val));
preserves call Yield_FTPreserved_20(tid, old(shadow.Lock), old(shadow.VC), old(sx.W), old(sx.R));
{
  var e, w, vw, r, vr: Epoch;

  call e := ThreadStateGetE(tid);

  // optional block
    call w := VarStateGetWNoLock(tid, x);
    if (w == e) {
      // write same epoch
      ok := true;
      return;
    }

  call Yield_FTRepOk_10() | Yield_FTPreserved_10(tid, old(shadow.Lock), old(shadow.VC), old(sx.W), old(sx.R));
  call Yield_FTRepOk_20() | Yield_FTPreserved_20(tid, old(shadow.Lock), old(shadow.VC), old(sx.W), old(sx.R));

  call AcquireVarLock(tid, x);
  call w := VarStateGetW(tid, x);
  call vw := VCGetElem(tid, ShadowableTid(tid->val), w->tid);
  if (!EpochLeq(w, vw)) {
    // write-write race
    call ReleaseVarLock(tid, x); ok := false; return;
  }
  call r := VarStateGetR(tid, x);
  if (r != SHARED) {
    call vr := VCGetElem(tid, ShadowableTid(tid->val), r->tid);
    if (!EpochLeq(r, vr)) {
      // read-write race
      call ReleaseVarLock(tid, x); ok := false; return;
    }
    // write exclusive
    call VarStateSetW(tid, x, e);
  } else {
    call ok := VC.Leq(tid, ShadowableVar(x), ShadowableTid(tid->val));
    if (!ok) {
      // shared-write race
      call ReleaseVarLock(tid, x);
      ok := false;
      return;
    }
    // write shared
    call VarStateSetW(tid, x, e);
  }

  call ReleaseVarLock(tid, x);
  ok := true;
  return;
}


atomic action {:layer 21,30} AtomicRead({:linear} tid: One Tid, x : Var) returns (ok : bool)
modifies sx.R, shadow.VC;
{
             var st : Shadowable;
             var sx : Shadowable;

             assert ValidTid(tid->val);
             assert tid->val != nil && tid->val >= 0;
             st := ShadowableTid(tid->val);
             sx := ShadowableVar(x);
             goto ReadSameEpoch, ReadSharedSameEpoch, ReadExclusive, ReadShared, ReadShare, WriteReadRace;
          ReadSameEpoch:
             ok := true;
             assume sx.R[x] == VCArrayGet(shadow.VC[st], tid->val);
             return;
          ReadSharedSameEpoch:
             ok := true;
             assume sx.R[x] == SHARED;
             assume VCArrayGet(shadow.VC[sx], tid->val) == VCArrayGet(shadow.VC[st], tid->val);
             return;
          ReadExclusive:
             ok := true;
             assume sx.R[x] != SHARED;
             assume EpochLeq(sx.W[x], VCArrayGet(shadow.VC[st], sx.W[x]->tid));
             assume EpochLeq(sx.R[x], VCArrayGet(shadow.VC[st], sx.R[x]->tid));
             sx.R[x] := VCArrayGet(shadow.VC[st], tid->val);
             return;
          ReadShared:
             ok := true;
             assume sx.R[x] == SHARED;
             assume EpochLeq(sx.W[x], VCArrayGet(shadow.VC[st], sx.W[x]->tid));
             shadow.VC[sx][tid->val] := VCArrayGet(shadow.VC[st], tid->val);
             shadow.VC[sx] := VCArraySetLen(shadow.VC[sx], max(VCArrayLen(shadow.VC[sx]), tid->val + 1));
             return;
          ReadShare:
             assume sx.R[x] != SHARED;
             assume EpochLeq(sx.W[x], VCArrayGet(shadow.VC[st], sx.W[x]->tid));
             shadow.VC[sx] := VC.bottom();
             shadow.VC[sx][sx.R[x]->tid] := sx.R[x];
             shadow.VC[sx][tid->val] := VCArrayGet(shadow.VC[st], tid->val);
             shadow.VC[sx] := VCArraySetLen(shadow.VC[sx], max(sx.R[x]->tid + 1, tid->val + 1));
             sx.R[x] := SHARED;
             ok := true;
             return;
          WriteReadRace:
             ok := false;
             assume !EpochLeq(sx.W[x], VCArrayGet(shadow.VC[st], sx.W[x]->tid));
             return;
}

yield procedure {:layer 20}
Read({:linear} tid: One Tid, x : Var) returns (ok : bool)
refines AtomicRead;
preserves call Yield_FTRepOk_10();
preserves call Yield_FTPreserved_10(tid, old(shadow.Lock), old(shadow.VC), old(sx.W), old(sx.R));
preserves call Yield_FTRepOk_20();
requires  call Yield_Lock_20(tid, ShadowableTid(tid->val));
preserves call Yield_FTPreserved_20(tid, old(shadow.Lock), old(shadow.VC), old(sx.W), old(sx.R));
{
  var e, w, vw, r, vr: Epoch;
  var xVC, stVC: VC;

  call e := ThreadStateGetE(tid);

   // optional block
     if (*) {
       // read same epoch
       call r := VarStateGetRNoLock(tid, x);
       assume r != SHARED;
       if (r == e) {
         ok := true;
         return;
       }
     } else {
       call r := VarStateGetRShared(tid, x);
       assume r == SHARED;
       call vw := VCGetElemShared(tid, x);
       if (vw == e) {
         ok := true;
         return;
       }
     }

  call Yield_FTRepOk_10() | Yield_FTPreserved_10(tid, old(shadow.Lock), old(shadow.VC), old(sx.W), old(sx.R));
  call Yield_FTRepOk_20() | Yield_FTPreserved_20(tid, old(shadow.Lock), old(shadow.VC), old(sx.W), old(sx.R));

  call AcquireVarLock(tid, x);
  call w := VarStateGetW(tid, x);
  call vw := VCGetElem(tid, ShadowableTid(tid->val), w->tid);
  if (!EpochLeq(w, vw)) {
    // write-read race
    call ReleaseVarLock(tid, x);
    ok := false;
    return;
  }
  call r := VarStateGetR(tid, x);
  if (r != SHARED) {
    call vr := VCGetElem(tid, ShadowableTid(tid->val), r->tid);
    if (EpochLeq(r, vr)) {
      // Read Exclusive
      assert {:layer 10,20} e->tid >= 0;
      call VarStateSetR(tid, x, e);
      call ReleaseVarLock(tid, x);
      ok := true;
      return;
    } else {
      call VCInit(tid, ShadowableVar(x));
      call VCSetElem(tid, ShadowableVar(x), r->tid, r);
      call VCSetElem(tid, ShadowableVar(x), tid->val, e);
      call VarStateSetR(tid, x, SHARED);
      call ReleaseVarLock(tid, x);
      ok := true;
      return;
    }
  } else {
      // Read Shared
      call VCSetElemShared(tid, x, e);
      call ReleaseVarLock(tid, x);
      ok := true;
      return;
  }
}


/****** Layer 30 --> 40 ******/

yield invariant {:layer 30} Yield_Lock_30({:linear} tid: One Tid, v: Shadowable);
preserves ValidTid(tid->val);
preserves shadow.Lock[v] == tid->val;

yield invariant {:layer 30} Yield_ThreadState_30({:linear} tid: One Tid);
preserves ValidTid(tid->val);
preserves thread.State[tid->val] == RUNNING();
preserves (forall t: Tid :: thread.State[t] == UNUSED() ==> shadow.Lock[ShadowableTid(t)] == nil);

yield invariant {:layer 30} Yield_Preserved_30({:linear} tid: One Tid, old.shadow.Lock: [Shadowable]Tid, old.thread.State: [Tid]ThreadStatus);
preserves ValidTid(tid->val);
preserves LocksPreserved(tid->val, old.shadow.Lock, shadow.Lock);
preserves (forall t: Tid :: old.shadow.Lock[ShadowableTid(t)] == tid->val ==> thread.State[t] == old.thread.State[t]);

yield procedure {:layer 30}
Driver({:linear} tid: One Tid) returns (ok: bool)
requires call Yield_Lock_10(tid, ShadowableTid(tid->val));
requires call Yield_FTRepOk_10();
requires call Yield_Lock_20(tid, ShadowableTid(tid->val));
requires call Yield_FTRepOk_20();
requires call Yield_Lock_30(tid, ShadowableTid(tid->val));
requires call Yield_ThreadState_30(tid);
{
  var x: Var;
  var l: Lock;
  var uid: Tid;

  ok := true;
  while (ok)
    invariant {:yields} true;
    invariant call Yield_Lock_10(tid, ShadowableTid(tid->val));
    invariant call Yield_FTRepOk_10();
    invariant call Yield_Lock_20(tid, ShadowableTid(tid->val));
    invariant call Yield_FTRepOk_20();
    invariant call Yield_Lock_30(tid, ShadowableTid(tid->val));
    invariant call Yield_ThreadState_30(tid);
  {
    if (*) {
      havoc x;
      call ok := Write(tid, x);
    } else if (*) {
      havoc x;
      call ok := Read(tid, x);
    } else if (*) {
      assert {:layer 10,20} shadow.Lock[ShadowableTid(tid->val)] == tid->val;
      call l := ChooseLockToAcquire(tid);
      call Yield_ThreadState_30(tid) | Yield_Preserved_30(tid, shadow.Lock, thread.State);
      call Acquire(tid, l);
    } else if (*) {
      call l := ChooseLockToRelease(tid);
      call Yield_ThreadState_30(tid) | Yield_Preserved_30(tid, shadow.Lock, thread.State);
      call Release(tid, l);
      call Yield_ThreadState_30(tid) | Yield_Preserved_30(tid, shadow.Lock, thread.State);
      call ReleaseChosenLock(tid, l);
    } else if (*) {
      call uid := AllocTid(tid);
      assert {:layer 10,20} shadow.Lock[ShadowableTid(tid->val)] == tid->val;
      assert {:layer 10,20} shadow.Lock[ShadowableTid(uid)] == tid->val;
      assert {:layer 10,20} (forall s: Shadowable :: VCRepOk(shadow.VC[s]));
      assert {:layer 10,20,30} tid->val != uid;
      assert {:layer 10,20,30} ValidTid(tid->val);
      assert {:layer 10,20,30} ValidTid(uid);
      call Yield_ThreadState_30(tid) | Yield_Preserved_30(tid, shadow.Lock, thread.State);
      assert {:layer 10,20,30} ValidTid(tid->val);
      assert {:layer 10,20,30} ValidTid(uid);
      call Fork(tid, uid);
      call Yield_ThreadState_30(tid) | Yield_Preserved_30(tid, shadow.Lock, thread.State);
      call StartThread(tid, uid);
    } else {
      call uid := ChooseThreadToJoin(tid);
      call Yield_ThreadState_30(tid) | Yield_Preserved_30(tid, shadow.Lock, thread.State);
      call Join(tid, uid);
      call Yield_ThreadState_30(tid) | Yield_Preserved_30(tid, shadow.Lock, thread.State);
      call ReleaseJoinLock(tid, uid);
    }
    assert {:layer 20} shadow.Lock[ShadowableTid(tid->val)] == tid->val;
  }
}

yield procedure {:layer 0} ReleaseJoinLock({:linear} tid: One Tid, uid: Tid);
refines AtomicReleaseJoinLock;
atomic action {:layer 1,30} AtomicReleaseJoinLock({:linear} tid: One Tid, uid: Tid)
modifies shadow.Lock;
{
    assert ValidTid(tid->val);
    assert ValidTid(uid);
    assert tid->val != uid;
    assert shadow.Lock[ShadowableTid(uid)] == tid->val;
    shadow.Lock[ShadowableTid(uid)] := nil;
}

yield procedure {:layer 0} ChooseThreadToJoin({:linear} tid: One Tid) returns (uid: Tid);
refines AtomicChooseThreadToJoin;
atomic action {:layer 1,30} AtomicChooseThreadToJoin({:linear} tid: One Tid) returns (uid: Tid)
modifies shadow.Lock, thread.HasJoined;
{
    assert thread.State[tid->val] == RUNNING() && ValidTid(tid->val);
    assume tid->val != uid;
    assume thread.State[uid] == STOPPED() && ValidTid(uid);
    assume shadow.Lock[ShadowableTid(uid)] == nil;
    shadow.Lock[ShadowableTid(uid)] := tid->val;
    thread.HasJoined[tid->val, uid] := true;
}

yield procedure {:layer 0} AllocTid({:linear} tid: One Tid) returns (uid: Tid);
refines AtomicAllocTid;
atomic action {:layer 1,30} AtomicAllocTid({:linear} tid: One Tid) returns (uid: Tid)
modifies thread.State, thread.ForkedBy, shadow.Lock;
{
    assert thread.State[tid->val] == RUNNING() && ValidTid(tid->val);
    assert (forall t: Tid :: thread.State[t] == UNUSED() ==> shadow.Lock[ShadowableTid(t)] == nil);
    assume tid->val != uid;
    assume thread.State[uid] == UNUSED() && ValidTid(uid);
    thread.State[uid] := NEW();
    thread.ForkedBy[uid] := tid->val;
    shadow.Lock[ShadowableTid(uid)] := tid->val;
    assume VCRepOk(shadow.VC[ShadowableTid(uid)]);
}

yield procedure {:layer 0} StartThread({:linear} tid: One Tid, uid: Tid);
refines AtomicStartThread;
atomic action {:layer 1,30} AtomicStartThread({:linear} tid: One Tid, uid: Tid)
modifies thread.State, shadow.Lock;
{
    assert ValidTid(tid->val);
    assert ValidTid(uid);
    assert tid->val != uid;
    assert shadow.Lock[ShadowableTid(uid)] == tid->val;
    assert thread.State[uid] == NEW();
    thread.State[uid] := RUNNING();
    shadow.Lock[ShadowableTid(uid)] := uid;
}

yield procedure {:layer 0} ChooseLockToAcquire({:linear} tid: One Tid) returns (l: Lock);
refines AtomicChooseLockToAcquire;
atomic action {:layer 1,30} AtomicChooseLockToAcquire({:linear} tid: One Tid) returns (l: Lock)
modifies shadow.Lock;
{
    assert ValidTid(tid->val);
    assume shadow.Lock[ShadowableLock(l)] == nil;
    shadow.Lock[ShadowableLock(l)] := tid->val;
}

yield procedure {:layer 0} ChooseLockToRelease({:linear} tid: One Tid) returns (l: Lock);
refines AtomicChooseLockToRelease;
atomic action {:layer 1,30} AtomicChooseLockToRelease({:linear} tid: One Tid) returns (l: Lock)
{
    assert ValidTid(tid->val);
    assume shadow.Lock[ShadowableLock(l)] == tid->val;
}

yield procedure {:layer 0} ReleaseChosenLock({:linear} tid: One Tid, l: Lock);
refines AtomicReleaseChosenLock;
atomic action {:layer 1,30} AtomicReleaseChosenLock({:linear} tid: One Tid, l: Lock)
modifies shadow.Lock;
{
    assert ValidTid(tid->val);
    assert shadow.Lock[ShadowableLock(l)] == tid->val;
    shadow.Lock[ShadowableLock(l)] := nil;
}
