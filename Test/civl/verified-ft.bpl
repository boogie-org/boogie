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
 * Proof of VerifiedFT correctness in CIVL.
 */

// RUN: %boogie -noinfer -useArrayTheory "%s" > "%t"
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
type{:datatype} Epoch;
function{:constructor} epoch(tid:Tid, clock:int):Epoch;

const unique SHARED: Epoch;

function {:inline} EpochInc(e : Epoch): Epoch {
  epoch(tid#epoch(e),clock#epoch(e) + 1)
}

function {:inline} EpochIsShared(e : Epoch): bool {
  e == SHARED
}

function {:inline} EpochLeq(e1 : Epoch, e2 : Epoch): bool {
  tid#epoch(e1) == tid#epoch(e2) && clock#epoch(e1) <=  clock#epoch(e2)
}

function {:inline} max(a : int, b : int) : int {
  if (a < b) then b else a
}

function {:inline} EpochMax(e1 : Epoch, e2 : Epoch): Epoch {
  epoch(tid#epoch(e1), max(clock#epoch(e1), clock#epoch(e2)))
}

function {:inline} EpochInit(tid: Tid): Epoch {
  epoch(tid, 0)
}


/*
 * VC
 */
type VC = [Tid]Epoch;

// primite accessors to array
// len of VC is stored at -1.
function {:inline} VCArrayLen(vc: VC): int { clock#epoch(vc[-1]) }
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
type{:datatype} Shadowable;
function {:constructor} ShadowableTid(tid: Tid): Shadowable;
function {:constructor} ShadowableLock(l: Lock): Shadowable;
function {:constructor} ShadowableVar(x: Var): Shadowable;

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
  (forall v: Var :: ValidTid(tid#epoch(w[v]))) &&
  (forall v: Var :: r[v] == SHARED || (tid#epoch(r[v]) >= 0 && tid#epoch(r[v]) != nil))
}

function {:inline false} VCRepOk(vc: VC): bool { 
  VCArrayLen(vc) >= 0 &&
  (forall j: int :: {vc[j]} 0 <= j && j < VCArrayLen(vc) ==> clock#epoch(vc[j]) >= 0) &&
  (forall j: int :: {vc[j]} 0 <= j && j < VCArrayLen(vc) ==> tid#epoch(vc[j]) == j) &&
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
function {:inline} LocksPreserved({:linear "tid" } tid: Tid, oldLocks: [Shadowable] Tid, locks: [Shadowable]Tid): bool {
  (forall v: Shadowable :: oldLocks[v] == tid ==> locks[v] == tid)
}

function {:inline} SharedInvPreserved(oldR: [Var] Epoch, r: [Var] Epoch): bool {
  (forall x: Var :: oldR[x] == SHARED ==> r[x] == SHARED) 
}

function {:inline} FTPreserved({:linear "tid" } tid:Tid,
	 	  	              oldLocks: [Shadowable] Tid, oldVcs: [Shadowable]VC, oldW: [Var]Epoch, oldR: [Var]Epoch,
	 	  	              locks: [Shadowable] Tid, 	  vcs: [Shadowable]VC, 	  w: [Var]Epoch,    r: [Var]Epoch): bool {
  LocksPreserved(tid, oldLocks, locks) && 
  SharedInvPreserved(oldR, r) &&
  (forall s: Shadowable :: oldLocks[s] == tid ==> vcs[s] == oldVcs[s]) && 
  (forall x: Var :: oldLocks[ShadowableVar(x)] == tid ==> r[x] == oldR[x]) &&
  (forall x: Var :: oldLocks[ShadowableVar(x)] == tid ==> w[x] == oldW[x])
}

/****** Layer 0  ******/

// VarState Lock
procedure {:yields}  {:layer 0} {:refines "AtomicAcquireVarLock"} AcquireVarLock({:linear "tid"} tid: Tid, x : Var);
procedure {:right} {:layer 1,20} AtomicAcquireVarLock({:linear "tid"} tid: Tid, x : Var)
modifies shadow.Lock;
{ assert ValidTid(tid); assume shadow.Lock[ShadowableVar(x)] == nil; shadow.Lock[ShadowableVar(x)] := tid; }

procedure {:yields} {:layer 0} {:refines "AtomicReleaseVarLock"} ReleaseVarLock({:linear "tid"} tid: Tid, x : Var);
procedure {:left} {:layer 1,20} AtomicReleaseVarLock({:linear "tid"} tid: Tid, x : Var)
modifies shadow.Lock;
{ assert ValidTid(tid); assert shadow.Lock[ShadowableVar(x)] == tid; shadow.Lock[ShadowableVar(x)] := nil; }


// ThreadState
procedure {:yields} {:layer 0} {:refines "AtomicThreadStateGetE"} ThreadStateGetE({:linear "tid"} tid: Tid) returns (e:Epoch);
procedure {:both} {:layer 1,20} AtomicThreadStateGetE({:linear "tid"} tid: Tid) returns (e:Epoch)
{ assert ValidTid(tid); assert shadow.Lock[ShadowableTid(tid)] == tid; e := shadow.VC[ShadowableTid(tid)][tid]; }


// VarState
procedure {:yields} {:layer 0} {:refines "AtomicVarStateSetW"} VarStateSetW({:linear "tid"} tid:Tid, x : Var, e:Epoch);
procedure {:atomic} {:layer 1,20} AtomicVarStateSetW({:linear "tid"} tid:Tid, x : Var, e:Epoch)
modifies sx.W;
{ assert ValidTid(tid); assert shadow.Lock[ShadowableVar(x)] == tid; sx.W[x] := e; }

procedure {:yields} {:layer 0} {:refines "AtomicVarStateGetW"} VarStateGetW({:linear "tid"} tid:Tid, x : Var) returns (e:Epoch);
procedure {:both} {:layer 1,20} AtomicVarStateGetW({:linear "tid"} tid:Tid, x : Var) returns (e:Epoch)
{ assert ValidTid(tid); assert shadow.Lock[ShadowableVar(x)] == tid; e := sx.W[x]; }

procedure {:yields} {:layer 0} {:refines "AtomicVarStateGetWNoLock"} VarStateGetWNoLock({:linear "tid"} tid:Tid, x : Var) returns (e:Epoch);
procedure {:atomic} {:layer 1,20} AtomicVarStateGetWNoLock({:linear "tid"} tid:Tid, x : Var) returns (e:Epoch)
{ assert ValidTid(tid); e := sx.W[x]; }

procedure {:yields} {:layer 0} {:refines "AtomicVarStateSetR"} VarStateSetR({:linear "tid"} tid:Tid, x : Var, e:Epoch);
procedure {:atomic} {:layer 1,20} AtomicVarStateSetR({:linear "tid"} tid:Tid, x : Var, e:Epoch)
modifies sx.R;
{ assert ValidTid(tid); assert shadow.Lock[ShadowableVar(x)] == tid; assert sx.R[x] != SHARED; sx.R[x] := e; }

procedure {:yields} {:layer 0} {:refines "AtomicVarStateGetRNoLock"} VarStateGetRNoLock({:linear "tid"} tid:Tid, x : Var) returns (e:Epoch);
procedure {:atomic} {:layer 1,20} AtomicVarStateGetRNoLock({:linear "tid"} tid:Tid, x : Var) returns (e:Epoch)
{ assert ValidTid(tid); e := sx.R[x]; }

procedure {:yields} {:layer 0} {:refines "AtomicVarStateGetR"} VarStateGetR({:linear "tid"} tid:Tid, x : Var) returns (e:Epoch);
procedure {:both} {:layer 1,20} AtomicVarStateGetR({:linear "tid"} tid:Tid, x : Var) returns (e:Epoch)
{ assert ValidTid(tid); assert shadow.Lock[ShadowableVar(x)] == tid; e := sx.R[x]; }

procedure {:yields} {:layer 0} {:refines "AtomicVarStateGetRShared"} VarStateGetRShared({:linear "tid"} tid:Tid, x : Var) returns (e:Epoch);
procedure {:right} {:layer 1,20} AtomicVarStateGetRShared({:linear "tid"} tid:Tid, x : Var) returns (e:Epoch)
{ assert ValidTid(tid); assume sx.R[x] == SHARED; e := SHARED; }


// VCs

procedure {:yields} {:layer 0} {:refines "AtomicVCGetSize"} VCGetSize({:linear "tid" } tid: Tid, r: Shadowable) returns (i: int);
procedure {:both} {:layer 1,10} AtomicVCGetSize({:linear "tid" } tid: Tid, r: Shadowable) returns (i: int)
{
   assert ValidTid(tid);
   assert (shadow.Lock[r] == tid);
   i := VCArrayLen(shadow.VC[r]);
}

procedure {:yields} {:layer 0} {:refines "AtomicVCGetElem"} VCGetElem({:linear "tid" } tid: Tid, r: Shadowable, i: int) returns (e: Epoch);
procedure {:both} {:layer 1,20} AtomicVCGetElem({:linear "tid" } tid: Tid, r: Shadowable, i: int) returns (e: Epoch)
{
   assert ValidTid(tid);
   assert (shadow.Lock[r] == tid);
   e := VCArrayGet(shadow.VC[r], i);
}

procedure {:yields} {:layer 0} {:refines "AtomicVCGetElemShared"} VCGetElemShared({:linear "tid" } tid: Tid, x : Var) returns (e: Epoch);
procedure {:atomic} {:layer 1,20} AtomicVCGetElemShared({:linear "tid" } tid: Tid, x : Var) returns (e: Epoch)
{
   assert sx.R[x] == SHARED;
   assert ValidTid(tid);
   e := VCArrayGet(shadow.VC[ShadowableVar(x)], tid);
}

procedure {:yields} {:layer 0} {:refines "AtomicVCSetElemShared"} VCSetElemShared({:linear "tid" } tid: Tid, x : Var, e: Epoch);
procedure {:both} {:layer 1,20} AtomicVCSetElemShared({:linear "tid" } tid: Tid, x : Var, e: Epoch)
modifies shadow.VC;
{
   assert sx.R[x] == SHARED; 
   assert ValidTid(tid); 
   assert (shadow.Lock[ShadowableVar(x)] == tid); 
   shadow.VC[ShadowableVar(x)][tid] := e;
   shadow.VC[ShadowableVar(x)] := VCArraySetLen(shadow.VC[ShadowableVar(x)], max(VCArrayLen(shadow.VC[ShadowableVar(x)]),tid+1));
}

procedure {:yields} {:layer 0} {:refines "AtomicVCSetElem"} VCSetElem({:linear "tid" } tid: Tid, r: Shadowable, i: int, e: Epoch);
procedure {:both} {:layer 1,20} AtomicVCSetElem({:linear "tid" } tid: Tid, r: Shadowable, i: int, e: Epoch)
modifies shadow.VC;
{
   assert is#ShadowableVar(r) ==> sx.R[x#ShadowableVar(r)] != SHARED; 
   assert ValidTid(tid); 
   assert (shadow.Lock[r] == tid); 
   shadow.VC[r][i] := e;
   shadow.VC[r] := VCArraySetLen(shadow.VC[r], max(VCArrayLen(shadow.VC[r]),i+1));
}

procedure {:yields} {:layer 0} {:refines "AtomicVCInit"} VCInit({:linear "tid" } tid: Tid, r: Shadowable);
procedure {:both} {:layer 1,20} AtomicVCInit({:linear "tid" } tid: Tid, r: Shadowable)
modifies shadow.VC;
{
   assert ValidTid(tid); 
   assert is#ShadowableVar(r) ==> sx.R[x#ShadowableVar(r)] != SHARED; 
   assert (shadow.Lock[r] == tid); 
   shadow.VC[r] := VC.bottom();
}


/****** Layer 10 -> 20 ******/

 procedure {:yields} {:layer 10} Yield10({:linear "tid"} tid:Tid)
     requires {:layer 10} ValidTid(tid);
     requires {:layer 10} FTRepOk(shadow.VC, sx.W, sx.R);
     ensures {:layer 10} LocksPreserved(tid, old(shadow.Lock), shadow.Lock);
     ensures {:layer 10} FTPreserved(tid, old(shadow.Lock), old(shadow.VC), old(sx.W), old(sx.R), shadow.Lock, shadow.VC, sx.W, sx.R);
     ensures {:layer 10} FTRepOk(shadow.VC, sx.W, sx.R);
 {
   yield;
   assert {:layer 10} ValidTid(tid);
   assert {:layer 10} LocksPreserved(tid, old(shadow.Lock), shadow.Lock);
   assert {:layer 10} FTPreserved(tid, old(shadow.Lock), old(shadow.VC), old(sx.W), old(sx.R), shadow.Lock, shadow.VC, sx.W, sx.R);
   assert {:layer 10} FTRepOk(shadow.VC, sx.W, sx.R);
 }

procedure {:both} {:layer 11,20} AtomicVC.Leq({:linear "tid"} tid: Tid, v1: Shadowable, v2: Shadowable) returns (res: bool)
{
   assert ValidTid(tid);
   assert shadow.Lock[v1] == tid;
   assert shadow.Lock[v2] == tid;
   assert shadow.Lock[ShadowableTid(tid)] == tid;
   assert is#ShadowableVar(v1) ==> sx.R[x#ShadowableVar(v1)] == SHARED;
   assert !is#ShadowableVar(v2);
   res := (forall j : int :: {f(j)} 0 <= j && f(j) ==> EpochLeq(VCArrayGet(shadow.VC[v1], j), VCArrayGet(shadow.VC[v2], j)));
}

procedure {:yields} {:layer 10} {:refines "AtomicVC.Leq"} VC.Leq({:linear "tid"} tid: Tid, v1: Shadowable, v2: Shadowable) returns (res: bool)
  requires {:layer 10} ValidTid(tid);
  requires {:layer 10} shadow.Lock[v1] == tid;
  requires {:layer 10} shadow.Lock[v2] == tid;
  requires {:layer 10} shadow.Lock[ShadowableTid(tid)] == tid;
  requires {:layer 10} FTRepOk(shadow.VC, sx.W, sx.R);
  requires {:layer 10} is#ShadowableVar(v1) ==> sx.R[x#ShadowableVar(v1)] == SHARED;
  requires {:layer 10} !is#ShadowableVar(v2);

  ensures {:layer 10} LocksPreserved(tid, old(shadow.Lock), shadow.Lock);
  ensures {:layer 10} FTPreserved(tid, old(shadow.Lock), old(shadow.VC), old(sx.W), old(sx.R), shadow.Lock, shadow.VC, sx.W, sx.R);
  ensures {:layer 10} FTRepOk(shadow.VC, sx.W, sx.R);
{
  var vc1, vc2: VC;
  var len1, len2 : int;
  var e1, e2: Epoch;
  var i: int;

  call Yield10(tid);

  call len1 := VCGetSize(tid, v1);
  call len2 := VCGetSize(tid, v1);

  i := 0;
  while (i < max(len1, len2)) 
    invariant {:layer 10} 0 <= i;
    invariant {:layer 10} (forall j : int :: {f(j)}
         0 <= j && j < i && f(j) ==>
         EpochLeq(VCArrayGet(shadow.VC[v1], j), VCArrayGet(shadow.VC[v2], j)));
  {
    call e1 := VCGetElem(tid, v1, i);    
    call e2 := VCGetElem(tid, v2, i);    
    if (!EpochLeq(e1, e2)) {
      assert {:layer 10} f(i);
      res := false;
      call Yield10(tid);
      return;
    }

    i := i + 1;
  }

  res := true;
  call Yield10(tid);
  return;
}

procedure {:both} {:layer 11,20} AtomicVC.Copy({:linear "tid"} tid: Tid, v1: Shadowable, v2: Shadowable)
modifies shadow.VC;
{
    var Vnew: VC;
    var shadow.VC.old : [Shadowable]VC; 

    assert ValidTid(tid);
    assert v1 != v2;
    assert shadow.Lock[ShadowableTid(tid)] == tid;
    assert shadow.Lock[v1] == tid;
    assert shadow.Lock[v2] == tid;
    assert !is#ShadowableVar(v1);	
    assert !is#ShadowableVar(v2);	
    assert VCRepOk(shadow.VC[v2]);
    assert VCRepOk(shadow.VC[v1]);
    if (*) {
        shadow.VC.old := shadow.VC; // save old state now
        shadow.VC[v1] := Vnew;
    	assume VCRepOk(Vnew);
    	assume VCArrayLen(shadow.VC[v1]) == max(VCArrayLen(shadow.VC.old[v1]),VCArrayLen(shadow.VC[v2]));
    	assume (forall j: int :: 0 <= j ==> VCArrayGet(shadow.VC[v1], j) == VCArrayGet(shadow.VC[v2], j));
    } else {
        shadow.VC[v1] := shadow.VC[v2];
    }
}

procedure {:yields} {:layer 10} {:refines "AtomicVC.Copy"} VC.Copy({:linear "tid"} tid: Tid, v1: Shadowable, v2: Shadowable)
  requires {:layer 10} ValidTid(tid);
  requires {:layer 10} v1 != v2;
  requires {:layer 10} shadow.Lock[ShadowableTid(tid)] == tid;
  requires {:layer 10} shadow.Lock[v1] == tid;
  requires {:layer 10} shadow.Lock[v2] == tid;
  requires {:layer 10} !is#ShadowableVar(v1);
  requires {:layer 10} !is#ShadowableVar(v2);
  requires {:layer 10} FTRepOk(shadow.VC, sx.W, sx.R);

  ensures {:layer 10} LocksPreserved(tid, old(shadow.Lock), shadow.Lock);
  ensures {:layer 10} FTRepOk(shadow.VC, sx.W, sx.R);
  ensures {:layer 10} (forall s: Shadowable :: s != v1 && old(shadow.Lock)[s] == tid ==> old(shadow.VC)[s] == shadow.VC[s]);
{
  var len1, len2 : int;
  var e1, e2: Epoch;
  var i: int;

  var {:layer 10} oldVC : [Shadowable] [Tid]Epoch;
  var {:layer 10} oldLock : [Shadowable] Tid;

  call Yield10(tid);

  call oldLock, oldVC := GhostRead();

  call len1 := VCGetSize(tid, v1);
  call len2 := VCGetSize(tid, v2);

  i := 0;
  while (i < max(len1, len2))
    invariant {:layer 10} (forall s: Shadowable :: s != v1 ==> shadow.VC[s] == oldVC[s]);
    invariant {:layer 10} (forall s: Shadowable :: oldLock[s] == tid ==> shadow.Lock[s] == tid);
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

  call Yield10(tid);
}


procedure {:right} {:layer 11,20} AtomicVC.Join({:linear "tid"} tid: Tid, v1: Shadowable, v2: Shadowable)
modifies shadow.VC;
{
    var shadow.VC.old: [Shadowable] VC;
    var vcNew: VC;

    assert ValidTid(tid);
    assert shadow.Lock[ShadowableTid(tid)] == tid;
    assert shadow.Lock[v1] == tid;
    assert shadow.Lock[v2] == tid;
    assert !is#ShadowableVar(v1);	
    assert !is#ShadowableVar(v2);	
    assert VCRepOk(shadow.VC[v2]);
    shadow.VC.old := shadow.VC;
    shadow.VC[v1] := vcNew;    
    assume VCRepOk(shadow.VC[v1]);
    assume VCArrayLen(shadow.VC[v1]) == max(VCArrayLen(shadow.VC.old[v1]),VCArrayLen(shadow.VC.old[v2]));
    assume (forall j: int :: 0 <= j ==> VCArrayGet(shadow.VC[v1], j) == EpochMax(VCArrayGet(shadow.VC.old[v1], j), VCArrayGet(shadow.VC[v2], j)));
}

procedure {:yields} {:layer 10} {:refines "AtomicVC.Join"} VC.Join({:linear "tid"} tid: Tid, v1: Shadowable, v2: Shadowable)
  requires {:layer 10} ValidTid(tid);
  requires {:layer 10} shadow.Lock[ShadowableTid(tid)] == tid;
  requires {:layer 10} shadow.Lock[v1] == tid;
  requires {:layer 10} shadow.Lock[v2] == tid;
  requires {:layer 10} !is#ShadowableVar(v1);
  requires {:layer 10} !is#ShadowableVar(v2);
  requires {:layer 10} FTRepOk(shadow.VC, sx.W, sx.R);

  ensures {:layer 10} LocksPreserved(tid, old(shadow.Lock), shadow.Lock);
  ensures {:layer 10} FTRepOk(shadow.VC, sx.W, sx.R);
  ensures {:layer 10} (forall s: Shadowable :: s != v1 && old(shadow.Lock)[s] == tid ==> old(shadow.VC)[s] == shadow.VC[s]);
{
  var len1, len2 : int;
  var e1, e2: Epoch;
  var i: int;

  var {:layer 10} oldVC : [Shadowable] [Tid]Epoch;
  var {:layer 10} oldLock : [Shadowable] Tid;

  call Yield10(tid);

  call oldLock, oldVC := GhostRead();

  call len1 := VCGetSize(tid, v1);
  call len2 := VCGetSize(tid, v2);

  i := 0;
  while (i < max(len1, len2))
    invariant {:layer 10} (forall s: Shadowable :: s != v1 ==> shadow.VC[s] == oldVC[s]);
    invariant {:layer 10} (forall s: Shadowable :: oldLock[s] == tid ==> shadow.Lock[s] == tid);
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

  call Yield10(tid);
}


procedure {:layer 10} GhostRead() returns (lock : [Shadowable]Tid, data : [Shadowable] [Tid]Epoch)
  ensures lock == shadow.Lock;
  ensures data == shadow.VC;
{
  lock := shadow.Lock;
  data := shadow.VC;
}

procedure {:both} {:layer 11,20} AtomicVC.Inc({:linear "tid" } tid: Tid, v: Shadowable, i: int)
modifies shadow.VC;
{
   assert ValidTid(tid);
   assert shadow.Lock[ShadowableTid(tid)] == tid;
   assert shadow.Lock[v] == tid;
   assert !is#ShadowableVar(v);
   assert i >= 0;
   assert VCRepOk(shadow.VC[v]);
   shadow.VC[v] := VCArraySetLen(shadow.VC[v], max(VCArrayLen(shadow.VC[v]), i+1));
   shadow.VC[v] := shadow.VC[v][i := EpochInc(shadow.VC[v][i])];
}

procedure {:yields} {:layer 10} {:refines "AtomicVC.Inc"} VC.Inc({:linear "tid" } tid: Tid, v: Shadowable, i: int)
  requires {:layer 10} ValidTid(tid);
  requires {:layer 10} shadow.Lock[ShadowableTid(tid)] == tid;
  requires {:layer 10} shadow.Lock[v] == tid;
  requires {:layer 10} !is#ShadowableVar(v);
  requires {:layer 10} FTRepOk(shadow.VC, sx.W, sx.R);
  requires {:layer 10} VCRepOk(shadow.VC[v]);
  requires {:layer 10} i >= 0;

  ensures {:layer 10} LocksPreserved(tid, old(shadow.Lock), shadow.Lock);
  ensures {:layer 10} FTRepOk(shadow.VC, sx.W, sx.R);
  ensures {:layer 10} VCRepOk(shadow.VC[v]);
  ensures {:layer 10} (forall s: Shadowable :: s != v && old(shadow.Lock)[s] == tid ==> old(shadow.VC)[s] == shadow.VC[s]);
{
  var e: Epoch;

  call Yield10(tid);

  call e := VCGetElem(tid, v, i);

  call VCSetElem(tid, v, i, EpochInc(e));

  call Yield10(tid);
}



/****** Layer 20 --> 30 ******/


procedure {:yields} {:layer 20} Yield20({:linear "tid"} tid:Tid)
    requires {:layer 10,20} ValidTid(tid);
    requires {:layer 10,20} shadow.Lock[ShadowableTid(tid)] == tid;
    requires {:layer 10,20} FTRepOk(shadow.VC, sx.W, sx.R);

    ensures {:layer 10,20} LocksPreserved(tid, old(shadow.Lock), shadow.Lock);
    ensures {:layer 10,20} FTPreserved(tid, old(shadow.Lock), old(shadow.VC), old(sx.W), old(sx.R), shadow.Lock, shadow.VC, sx.W, sx.R);
    ensures {:layer 10,20} FTRepOk(shadow.VC, sx.W, sx.R);
{
    yield;
    assert {:layer 10,20} ValidTid(tid);
    assert {:layer 10,20} LocksPreserved(tid, old(shadow.Lock), shadow.Lock);
    assert {:layer 10,20} FTPreserved(tid, old(shadow.Lock), old(shadow.VC), old(sx.W), old(sx.R), shadow.Lock, shadow.VC, sx.W, sx.R);
    assert {:layer 10,20} FTRepOk(shadow.VC, sx.W, sx.R);
}


procedure {:atomic} {:layer 21,30} AtomicFork({:linear "tid"} tid:Tid, uid : Tid)
modifies shadow.VC;
{
    var shadow.VC.old: [Shadowable] VC;
    var vcNew,vcNew2: VC;
    var v1,v2: Shadowable;

    assert ValidTid(tid);
    assert ValidTid(uid);
    assert shadow.Lock[ShadowableTid(tid)] == tid;
    assert shadow.Lock[ShadowableTid(uid)] == tid;
    assert tid != uid;

    v1 := ShadowableTid(uid);
    v2 := ShadowableTid(tid);
    shadow.VC.old := shadow.VC;
    shadow.VC[v1] := vcNew;    
    assume VCArrayLen(vcNew) == max(VCArrayLen(shadow.VC.old[v1]),VCArrayLen(shadow.VC.old[v2]));
    assume VCRepOk(shadow.VC[v1]);
    assume (forall j: int :: 0 <= j ==> VCArrayGet(shadow.VC[v1], j) == EpochMax(VCArrayGet(shadow.VC.old[v1], j), VCArrayGet(shadow.VC[v2], j)));

    shadow.VC[ShadowableTid(tid)] := vcNew2;
    assume VCRepOk(vcNew2);
    assume VCArrayLen(vcNew2) == max(VCArrayLen(shadow.VC[ShadowableTid(tid)]), tid+1);
    assume (forall j: int :: 0 <= j && j != tid ==> VCArrayGet(shadow.VC[ShadowableTid(tid)], j) == 
    	   	      	       	    	VCArrayGet(shadow.VC.old[ShadowableTid(tid)], j));
    assume VCArrayGet(shadow.VC[ShadowableTid(tid)], tid) == 
    	   EpochInc(VCArrayGet(shadow.VC.old[ShadowableTid(tid)], tid));
}

procedure {:yields} {:layer 20} {:refines "AtomicFork"} Fork({:linear "tid"} tid:Tid, uid : Tid)
  requires {:layer 10,20} ValidTid(tid);
  requires {:layer 10,20} ValidTid(uid);
  requires {:layer 10,20} shadow.Lock[ShadowableTid(tid)] == tid;
  requires {:layer 10,20} shadow.Lock[ShadowableTid(uid)] == tid;
  requires {:layer 10,20} tid != uid;
  requires {:layer 10,20} FTRepOk(shadow.VC, sx.W, sx.R);

  ensures {:layer 10,20} LocksPreserved(tid, old(shadow.Lock), shadow.Lock);
  ensures {:layer 10,20} FTRepOk(shadow.VC, sx.W, sx.R);
  ensures {:layer 10,20} (forall s: Shadowable :: s != ShadowableTid(tid) && 
  	  	     	     		      s != ShadowableTid(uid) ==>
					      (old(shadow.Lock)[s] == tid ==> old(shadow.VC)[s] == shadow.VC[s]));
{
  call Yield20(tid);

  call VC.Join(tid, ShadowableTid(uid), ShadowableTid(tid));

  call VC.Inc(tid, ShadowableTid(tid), tid);

  call Yield20(tid);
}


procedure {:atomic} {:layer 21,30} AtomicJoin({:linear "tid"} tid:Tid, uid : Tid)
modifies shadow.VC;
{
    var shadow.VC.old: [Shadowable] VC;
    var vcNew: VC;
    var v1, v2: Shadowable;

    assert ValidTid(tid);
    assert ValidTid(uid);
    assert shadow.Lock[ShadowableTid(tid)] == tid;
    assert shadow.Lock[ShadowableTid(uid)] == tid;
    assert tid != uid;

    v1 := ShadowableTid(uid);
    v2 := ShadowableTid(tid);

    shadow.VC.old := shadow.VC;
    shadow.VC[ShadowableTid(tid)] := vcNew;    
    assume VCArrayLen(vcNew) == max(VCArrayLen(shadow.VC.old[v1]),VCArrayLen(shadow.VC.old[v2]));
    assume VCRepOk(shadow.VC[ShadowableTid(tid)]);
    assume (forall j: int :: 0 <= j ==> 
    	   VCArrayGet(shadow.VC[ShadowableTid(tid)], j) == 
	   EpochMax(VCArrayGet(shadow.VC.old[ShadowableTid(tid)], j), VCArrayGet(shadow.VC[ShadowableTid(uid)], j)));
}

procedure {:yields} {:layer 20} {:refines "AtomicJoin"} Join({:linear "tid"} tid:Tid, uid : Tid)
  requires {:layer 10,20} ValidTid(tid);
  requires {:layer 10,20} ValidTid(uid);
  requires {:layer 10,20} shadow.Lock[ShadowableTid(tid)] == tid;
  requires {:layer 10,20} shadow.Lock[ShadowableTid(uid)] == tid;
  requires {:layer 10,20} tid != uid;
  requires {:layer 10,20} FTRepOk(shadow.VC, sx.W, sx.R);

  ensures {:layer 10,20} LocksPreserved(tid, old(shadow.Lock), shadow.Lock);
  ensures {:layer 10,20} FTRepOk(shadow.VC, sx.W, sx.R);
  ensures {:layer 10,20} (forall s: Shadowable :: s != ShadowableTid(tid) && old(shadow.Lock)[s] == tid ==> old(shadow.VC)[s] == shadow.VC[s]);
{
  call Yield20(tid);
  call VC.Join(tid, ShadowableTid(tid), ShadowableTid(uid));
  call Yield20(tid);
}


procedure {:atomic} {:layer 21,30} AtomicAcquire({:linear "tid"} tid: Tid, l: Lock)
modifies shadow.VC;
{
    var shadow.VC.old: [Shadowable] VC;
    var vcNew: VC;
    var v1, v2: Shadowable;

    assert {:layer 10,20} ValidTid(tid);
    assert {:layer 10,20} shadow.Lock[ShadowableLock(l)] == tid;
    assert {:layer 10,20} shadow.Lock[ShadowableTid(tid)] == tid;

    v1 := ShadowableTid(tid);
    v2 := ShadowableLock(l);
    shadow.VC.old := shadow.VC;
    shadow.VC[v1] := vcNew;    
    assume VCRepOk(shadow.VC[v1]);
    assume VCArrayLen(vcNew) == max(VCArrayLen(shadow.VC.old[v1]),VCArrayLen(shadow.VC.old[v2]));
    assume (forall j: int :: 0 <= j ==> 
    	   VCArrayGet(shadow.VC[v1], j) == 
	   EpochMax(VCArrayGet(shadow.VC.old[v1], j), VCArrayGet(shadow.VC[v2], j)));
}

procedure {:yields} {:layer 20} {:refines "AtomicAcquire"} Acquire({:linear "tid"} tid: Tid, l: Lock)
  requires {:layer 10,20} ValidTid(tid);
  requires {:layer 10,20} shadow.Lock[ShadowableTid(tid)] == tid;
  requires {:layer 10,20} shadow.Lock[ShadowableLock(l)] == tid;
  requires {:layer 10,20} FTRepOk(shadow.VC, sx.W, sx.R);

  ensures {:layer 10,20} LocksPreserved(tid, old(shadow.Lock), shadow.Lock);
  ensures {:layer 10,20} FTRepOk(shadow.VC, sx.W, sx.R);
  ensures {:layer 10,20} (forall s: Shadowable :: s != ShadowableTid(tid) && old(shadow.Lock)[s] == tid ==> old(shadow.VC)[s] == shadow.VC[s]);
{
  call Yield20(tid);

  call VC.Join(tid, ShadowableTid(tid), ShadowableLock(l));

  call Yield20(tid);
}

procedure {:atomic} {:layer 21,30} AtomicRelease({:linear "tid"} tid: Tid, l: Lock)
modifies shadow.VC;
{
    var shadow.VC.old: [Shadowable] VC;
    var vcNew,vcNew2: VC;
    var v1,v2: Shadowable;

    assert ValidTid(tid);
    assert shadow.Lock[ShadowableTid(tid)] == tid;
    assert shadow.Lock[ShadowableLock(l)] == tid;

    v1 := ShadowableLock(l);
    v2 := ShadowableTid(tid);

    shadow.VC.old := shadow.VC;

    // Use the same strategy as in Copy's atomic spec.  
    if (*) {
        shadow.VC[v1] := vcNew;
    	assume VCRepOk(vcNew);
    	assume VCArrayLen(shadow.VC[v1]) == max(VCArrayLen(shadow.VC.old[v1]),VCArrayLen(shadow.VC[v2]));
    	assume (forall j: int :: 0 <= j ==> VCArrayGet(shadow.VC[v1], j) == VCArrayGet(shadow.VC[v2], j));
    } else {
        shadow.VC[v1] := shadow.VC[v2];
    }

    shadow.VC[v2] := vcNew2;
    assume VCRepOk(vcNew2);
    assume VCArrayLen(vcNew2) == max(VCArrayLen(shadow.VC[v2]), tid+1);
    assume (forall j: int :: 0 <= j && j != tid ==> VCArrayGet(shadow.VC[v2], j) == VCArrayGet(shadow.VC.old[v2], j));
    assume VCArrayGet(shadow.VC[v2], tid) == EpochInc(VCArrayGet(shadow.VC.old[v2], tid));
}

procedure {:yields} {:layer 20} {:refines "AtomicRelease"} Release({:linear "tid"} tid: Tid, l: Lock)
  requires {:layer 10,20} ValidTid(tid);
  requires {:layer 10,20} shadow.Lock[ShadowableTid(tid)] == tid;
  requires {:layer 10,20} shadow.Lock[ShadowableLock(l)] == tid;
  requires {:layer 10,20} FTRepOk(shadow.VC, sx.W, sx.R);

  ensures {:layer 10,20} LocksPreserved(tid, old(shadow.Lock), shadow.Lock);
  ensures {:layer 10,20} FTRepOk(shadow.VC, sx.W, sx.R);
  ensures {:layer 10,20} (forall s: Shadowable :: s != ShadowableTid(tid)  && s != ShadowableLock(l) && old(shadow.Lock)[s] == tid ==> old(shadow.VC)[s] == shadow.VC[s]);
{
  var sm : Shadowable;
  var st : Shadowable;

  call Yield20(tid);

  call VC.Copy(tid, ShadowableLock(l), ShadowableTid(tid));

  call VC.Inc(tid, ShadowableTid(tid), tid);

  call Yield20(tid);
}


procedure {:atomic} {:layer 21,30} AtomicWrite({:linear "tid"} tid:Tid, x : Var) returns (ok : bool)
modifies sx.W;
{
  	     var st : Shadowable;
  	     var sx : Shadowable;

             assert ValidTid(tid);
	     st := ShadowableTid(tid);
	     sx := ShadowableVar(x);
             goto WriteFastPath, WriteExclusive, WritedShared, WriteWriteRace, ReadWriteRace, SharedWriteRace;
          WriteFastPath:
             ok := true;
             assume sx.W[x] == VCArrayGet(shadow.VC[st], tid);
             return;
          WriteExclusive:
             ok := true;
             assume EpochLeq(sx.W[x], VCArrayGet(shadow.VC[st], tid#epoch(sx.W[x])));
             assume sx.R[x] != SHARED;
             assume EpochLeq(sx.R[x], VCArrayGet(shadow.VC[st], tid#epoch(sx.R[x])));
             sx.W[x] := VCArrayGet(shadow.VC[st], tid);
             return;
          WritedShared:
             ok := true;
             assume EpochLeq(sx.W[x], VCArrayGet(shadow.VC[st], tid#epoch(sx.W[x])));
             assume sx.R[x] == SHARED;
             assume (forall j : int :: {f(j)}
                      0 <= j && j < max(VCArrayLen(shadow.VC[sx]), VCArrayLen(shadow.VC[st])) && f(j) ==>
                      EpochLeq(VCArrayGet(shadow.VC[sx], j), VCArrayGet(shadow.VC[st], j)));
             sx.W[x] := VCArrayGet(shadow.VC[st], tid);
             return;
          WriteWriteRace:
             ok := false;
             assume !EpochLeq(sx.W[x], VCArrayGet(shadow.VC[st], tid#epoch(sx.W[x])));
             return;
          ReadWriteRace:
             ok := false;
             assume sx.R[x] != SHARED;
             assume !EpochLeq(sx.R[x], VCArrayGet(shadow.VC[st], tid#epoch(sx.R[x])));
             return;
          SharedWriteRace:
             ok := false;
             assume sx.R[x] == SHARED;
             assume !(forall j : int :: {f(j)}
                      0 <= j && j < max(VCArrayLen(shadow.VC[st]),VCArrayLen(shadow.VC[sx])) && f(j) ==>
                      EpochLeq(VCArrayGet(shadow.VC[sx], j), VCArrayGet(shadow.VC[st], j)));
             return;
}

procedure {:yields} {:layer 20} {:refines "AtomicWrite"} Write({:linear "tid"} tid:Tid, x : Var) returns (ok : bool)
  requires {:layer 10,20} ValidTid(tid);
  requires {:layer 10,20} shadow.Lock[ShadowableTid(tid)] == tid;
  requires {:layer 10,20} FTRepOk(shadow.VC, sx.W, sx.R);

  ensures {:layer 10,20} LocksPreserved(tid, old(shadow.Lock), shadow.Lock);
  ensures {:layer 10,20} FTRepOk(shadow.VC, sx.W, sx.R);
{
  var e, w, vw, r, vr: Epoch;

  call Yield20(tid);

  call e := ThreadStateGetE(tid);

  // optional block
    call w := VarStateGetWNoLock(tid, x);
    if (w == e) {
      // write same epoch
      ok := true;
      call Yield20(tid);
      return;
    }
   
  call Yield20(tid);

  call AcquireVarLock(tid, x);
  call w := VarStateGetW(tid, x);
  call vw := VCGetElem(tid, ShadowableTid(tid), tid#epoch(w));
  if (!EpochLeq(w, vw)) {
    // write-write race
    call ReleaseVarLock(tid, x); ok := false; call Yield20(tid); return;
  }
  call r := VarStateGetR(tid, x);
  if (r != SHARED) {
    call vr := VCGetElem(tid, ShadowableTid(tid), tid#epoch(r));
    if (!EpochLeq(r, vr)) {
      // read-write race
      call ReleaseVarLock(tid, x); ok := false; call Yield20(tid); return;
    }
    // write exclusive
    call VarStateSetW(tid, x, e);
  } else {
    call ok := VC.Leq(tid, ShadowableVar(x), ShadowableTid(tid));
    if (!ok) {
      // shared-write race
      call ReleaseVarLock(tid, x);
      ok := false;
      call Yield20(tid); return;
    }
    // write shared
    call VarStateSetW(tid, x, e);
  }

  call ReleaseVarLock(tid, x);
  ok := true;
  call Yield20(tid);
  return;
}


procedure {:atomic} {:layer 21,30} AtomicRead({:linear "tid"} tid:Tid, x : Var) returns (ok : bool)
modifies sx.R, shadow.VC;
{
   	     var st : Shadowable;
  	     var sx : Shadowable;
	     var vc : VC;

	     assert ValidTid(tid);
             assert tid != nil && tid >= 0 && tid >= 0;
	     st := ShadowableTid(tid);
	     sx := ShadowableVar(x);
             goto ReadSameEpoch, ReadSharedSameEpoch, ReadExclusive, ReadShared, ReadShare, WriteReadRace;
          ReadSameEpoch:
             ok := true;
             assume sx.R[x] == VCArrayGet(shadow.VC[st], tid);
             return;
          ReadSharedSameEpoch:
             ok := true;
             assume sx.R[x] == SHARED;
             assume VCArrayGet(shadow.VC[sx], tid) == VCArrayGet(shadow.VC[st], tid);
             return;
          ReadExclusive:
             ok := true;
             assume sx.R[x] != SHARED;
             assume EpochLeq(sx.W[x], VCArrayGet(shadow.VC[st], tid#epoch(sx.W[x])));
             assume EpochLeq(sx.R[x], VCArrayGet(shadow.VC[st], tid#epoch(sx.R[x])));
             sx.R[x] := VCArrayGet(shadow.VC[st], tid);
             return;
          ReadShared:
             ok := true;
             assume sx.R[x] == SHARED;
             assume EpochLeq(sx.W[x], VCArrayGet(shadow.VC[st], tid#epoch(sx.W[x])));
             shadow.VC[sx][tid] := VCArrayGet(shadow.VC[st], tid);
	     shadow.VC[sx] := VCArraySetLen(shadow.VC[sx], max(VCArrayLen(shadow.VC[sx]), tid+1));
             return;
          ReadShare:
             assume sx.R[x] != SHARED;
             assume EpochLeq(sx.W[x], VCArrayGet(shadow.VC[st], tid#epoch(sx.W[x])));
             shadow.VC[sx] := VC.bottom();
             shadow.VC[sx][tid#epoch(sx.R[x])] := sx.R[x];
             shadow.VC[sx][tid] := VCArrayGet(shadow.VC[st], tid);
	     shadow.VC[sx] := VCArraySetLen(shadow.VC[sx], max(tid#epoch(sx.R[x])+1, tid+1));
             sx.R[x] := SHARED;
             ok := true;
             return;
          WriteReadRace:
             ok := false;
             assume !EpochLeq(sx.W[x], VCArrayGet(shadow.VC[st], tid#epoch(sx.W[x])));
             return;
}

procedure {:yields} {:layer 20} {:refines "AtomicRead"} Read({:linear "tid"} tid:Tid, x : Var) returns (ok : bool)
  requires {:layer 10,20} ValidTid(tid);
  requires {:layer 10,20} shadow.Lock[ShadowableTid(tid)] == tid;
  requires {:layer 10,20} FTRepOk(shadow.VC, sx.W, sx.R);

  ensures {:layer 10,20} LocksPreserved(tid, old(shadow.Lock), shadow.Lock);
  ensures {:layer 10,20} FTRepOk(shadow.VC, sx.W, sx.R);
{
  var e, w, vw, r, vr: Epoch;
  var xVC, stVC: VC;

  call Yield20(tid);

  call e := ThreadStateGetE(tid);

   // optional block
     if (*) {
       // read same epoch
       call r := VarStateGetRNoLock(tid, x);
       assume r != SHARED;
       if (r == e) {
         ok := true;
         call Yield20(tid);
         return; 
       }
     } else {
       call r := VarStateGetRShared(tid, x);
       assume r == SHARED;
       call vw := VCGetElemShared(tid, x);
       if (vw == e) {
         ok := true;
         call Yield20(tid);
         return;
       }
     } 

  call Yield20(tid);

  call AcquireVarLock(tid, x);
  call w := VarStateGetW(tid, x);
  call vw := VCGetElem(tid, ShadowableTid(tid), tid#epoch(w));
  if (!EpochLeq(w, vw)) {
    // write-read race
    call ReleaseVarLock(tid, x); 
    ok := false; 
    call Yield20(tid); 
    return;
  }
  call r := VarStateGetR(tid, x);
  if (r != SHARED) {
    call vr := VCGetElem(tid, ShadowableTid(tid), tid#epoch(r));
    if (EpochLeq(r, vr)) {
      // Read Exclusive
      assert {:layer 10,20} tid#epoch(e) >= 0;
      call VarStateSetR(tid, x, e);
      call ReleaseVarLock(tid, x); 
      ok := true; 
      call Yield20(tid); 
      return;
    } else {
      call VCInit(tid, ShadowableVar(x));
      call VCSetElem(tid, ShadowableVar(x), tid#epoch(r), r);
      call VCSetElem(tid, ShadowableVar(x), tid, e); 
      call VarStateSetR(tid, x, SHARED); 
      call ReleaseVarLock(tid, x); 
      ok := true; 
      call Yield20(tid); 
      return;
    }
  } else {
      // Read Shared
      call VCSetElemShared(tid, x, e);
      call ReleaseVarLock(tid, x); 
      ok := true;
      call Yield20(tid);
      return;
  }
}


/****** Layer 30 --> 40 ******/



procedure {:yields} {:layer 30} Yield30({:linear "tid"} tid:Tid)
  requires {:layer 10,20,30} ValidTid(tid);
  requires {:layer 10,20} shadow.Lock[ShadowableTid(tid)] == tid;
  requires {:layer 10,20} FTRepOk(shadow.VC, sx.W, sx.R);

  requires {:layer 30} thread.State[tid] == RUNNING();
  requires {:layer 30} (forall t: Tid :: thread.State[t] == UNUSED() ==> shadow.Lock[ShadowableTid(t)] == nil);

  ensures {:layer 10,20,30} LocksPreserved(tid, old(shadow.Lock), shadow.Lock);
  ensures {:layer 10,20} FTRepOk(shadow.VC, sx.W, sx.R);

  ensures {:layer 30} thread.State[tid] == RUNNING();
  ensures {:layer 30} (forall t: Tid :: old(shadow.Lock)[ShadowableTid(t)] == tid ==> thread.State[t] == old(thread.State)[t]);
  ensures {:layer 30} (forall t: Tid :: thread.State[t] == UNUSED() ==> shadow.Lock[ShadowableTid(t)] == nil);
 
{
    yield;

    assert {:layer 10,20,30} ValidTid(tid);

    assert {:layer 10,20,30} LocksPreserved(tid, old(shadow.Lock), shadow.Lock);
    assert {:layer 10,20} FTRepOk(shadow.VC, sx.W, sx.R);

    assert {:layer 10,20} FTPreserved(tid, old(shadow.Lock), old(shadow.VC), old(sx.W), old(sx.R), shadow.Lock, shadow.VC, sx.W, sx.R);

    assert {:layer 30} thread.State[tid] == RUNNING();
    assert {:layer 30} (forall t: Tid :: old(shadow.Lock)[ShadowableTid(t)] == tid ==> thread.State[t] == old(thread.State)[t]);
    assert {:layer 30} (forall t: Tid :: thread.State[t] == UNUSED() ==> shadow.Lock[ShadowableTid(t)] == nil);
}


procedure {:yields} {:layer 30} Driver({:linear "tid"} tid:Tid) returns (ok: bool)
  requires {:layer 10,20,30} ValidTid(tid);
  requires {:layer 10,20,30} shadow.Lock[ShadowableTid(tid)] == tid;
  requires {:layer 10,20} (forall s: Shadowable :: VCRepOk(shadow.VC[s]));
  requires {:layer 10,20} VarsRepOk(sx.W, sx.R);	
  requires {:layer 30} thread.State[tid] == RUNNING();
  requires {:layer 30} (forall t: Tid :: thread.State[t] == UNUSED() ==> shadow.Lock[ShadowableTid(t)] == nil);
{
  var x: Var;
  var l: Lock;
  var uid: Tid;
  call Yield30(tid);
  ok := true;
  while (ok)
    invariant {:layer 10,20,30} ValidTid(tid);
    invariant {:layer 10,20,30} shadow.Lock[ShadowableTid(tid)] == tid;
    invariant {:layer 30} thread.State[tid] == RUNNING();
    invariant {:layer 10,20} (forall s: Shadowable :: VCRepOk(shadow.VC[s]));
    invariant {:layer 10,20} VarsRepOk(sx.W, sx.R);	
    invariant {:layer 30} (forall t: Tid :: thread.State[t] == UNUSED() ==> shadow.Lock[ShadowableTid(t)] == nil);
  {
    if (*) {
      havoc x;
      call ok := Write(tid, x);
    } else if (*) {
      havoc x;
      call ok := Read(tid, x);
    } else if (*) {
      assert {:layer 10,20} shadow.Lock[ShadowableTid(tid)] == tid;
      call l := ChooseLockToAcquire(tid);
      call Yield30(tid);
      call Acquire(tid, l);
    } else if (*) {
      call l := ChooseLockToRelease(tid);
      call Yield30(tid);
      call Release(tid, l);
      call Yield30(tid);
      call ReleaseChosenLock(tid, l);
      call Yield30(tid);
    } else if (*) {
      call uid := AllocTid(tid);
      assert {:layer 10,20} shadow.Lock[ShadowableTid(tid)] == tid;
      assert {:layer 10,20} shadow.Lock[ShadowableTid(uid)] == tid;
      assert {:layer 10,20} (forall s: Shadowable :: VCRepOk(shadow.VC[s]));
      assert {:layer 10,20,30} tid != uid;
      assert {:layer 10,20,30} ValidTid(tid);
      assert {:layer 10,20,30} ValidTid(uid);
      call Yield30(tid);
      assert {:layer 10,20,30} ValidTid(tid);
      assert {:layer 10,20,30} ValidTid(uid);
      call Fork(tid, uid);
      call Yield30(tid);
      call StartThread(tid, uid);
      call Yield30(tid);
    } else {
      call Yield30(tid);
      call uid := ChooseThreadToJoin(tid);
      call Yield30(tid);
      call Join(tid, uid);
      call Yield30(tid);
      call ReleaseJoinLock(tid, uid);
      call Yield30(tid);
    }
    call Yield30(tid);
    assert {:layer 20} shadow.Lock[ShadowableTid(tid)] == tid;
  }
  yield;
}

procedure {:yields} {:layer 0} {:refines "AtomicReleaseJoinLock"} ReleaseJoinLock({:linear "tid"} tid:Tid, uid: Tid);
procedure {:atomic} {:layer 1,30} AtomicReleaseJoinLock({:linear "tid"} tid:Tid, uid: Tid)
modifies shadow.Lock;
{
    assert ValidTid(tid);
    assert ValidTid(uid);
    assert tid != uid;
    assert shadow.Lock[ShadowableTid(uid)] == tid;
    shadow.Lock[ShadowableTid(uid)] := nil;
}

procedure {:yields} {:layer 0} {:refines "AtomicChooseThreadToJoin"} ChooseThreadToJoin({:linear "tid"} tid:Tid) returns (uid: Tid);
procedure {:atomic} {:layer 1,30} AtomicChooseThreadToJoin({:linear "tid"} tid:Tid) returns (uid: Tid)
modifies shadow.Lock, thread.HasJoined;
{
    assert thread.State[tid] == RUNNING() && ValidTid(tid);
    assume tid != uid;
    assume thread.State[uid] == STOPPED() && ValidTid(uid);
    assume shadow.Lock[ShadowableTid(uid)] == nil;
    shadow.Lock[ShadowableTid(uid)] := tid;
    thread.HasJoined[tid, uid] := true;
}

procedure {:yields} {:layer 0} {:refines "AtomicAllocTid"} AllocTid({:linear "tid"} tid:Tid) returns (uid: Tid);
procedure {:atomic} {:layer 1,30} AtomicAllocTid({:linear "tid"} tid:Tid) returns (uid: Tid)
modifies thread.State, thread.ForkedBy, shadow.Lock;
{
    assert thread.State[tid] == RUNNING() && ValidTid(tid);
    assert (forall t: Tid :: thread.State[t] == UNUSED() ==> shadow.Lock[ShadowableTid(t)] == nil);
    assume tid != uid;
    assume thread.State[uid] == UNUSED() && ValidTid(uid);
    thread.State[uid] := NEW();
    thread.ForkedBy[uid] := tid;
    shadow.Lock[ShadowableTid(uid)] := tid;
    assume VCRepOk(shadow.VC[ShadowableTid(uid)]);
}

procedure {:yields} {:layer 0} {:refines "AtomicStartThread"} StartThread({:linear "tid"} tid:Tid, uid: Tid);
procedure {:atomic} {:layer 1,30} AtomicStartThread({:linear "tid"} tid:Tid, uid: Tid)
modifies thread.State, shadow.Lock;
{
    assert ValidTid(tid);
    assert ValidTid(uid);
    assert tid != uid;
    assert shadow.Lock[ShadowableTid(uid)] == tid;
    assert thread.State[uid] == NEW();
    thread.State[uid] := RUNNING();
    shadow.Lock[ShadowableTid(uid)] := uid;
}

procedure {:yields} {:layer 0} {:refines "AtomicChooseLockToAcquire"} ChooseLockToAcquire({:linear "tid"} tid:Tid) returns (l: Lock);
procedure {:atomic} {:layer 1,30} AtomicChooseLockToAcquire({:linear "tid"} tid:Tid) returns (l: Lock)
modifies shadow.Lock;
{
    assert ValidTid(tid);
    assume shadow.Lock[ShadowableLock(l)] == nil;
    shadow.Lock[ShadowableLock(l)] := tid;
}

procedure {:yields} {:layer 0} {:refines "AtomicChooseLockToRelease"} ChooseLockToRelease({:linear "tid"} tid:Tid) returns (l: Lock);
procedure {:atomic} {:layer 1,30} AtomicChooseLockToRelease({:linear "tid"} tid:Tid) returns (l: Lock)
{
    assert ValidTid(tid);
    assume shadow.Lock[ShadowableLock(l)] == tid;
}

procedure {:yields} {:layer 0} {:refines "AtomicReleaseChosenLock"} ReleaseChosenLock({:linear "tid"} tid:Tid, l: Lock);
procedure {:atomic} {:layer 1,30} AtomicReleaseChosenLock({:linear "tid"} tid:Tid, l: Lock)
modifies shadow.Lock;
{
    assert ValidTid(tid);
    assert shadow.Lock[ShadowableLock(l)] == tid;
    shadow.Lock[ShadowableLock(l)] := nil;
}






// needed for linear Tids --- don't forget...
function {:builtin "MapConst"} TidMapConstBool(bool): [Tid]bool;

function {:inline} {:linear "tid"} TidCollector(x: Tid) : [Tid]bool
{
  TidMapConstBool(false)[x := true]
}

// for matching quantifiers 
function {:inline false} f(i: int): bool {  true  }

