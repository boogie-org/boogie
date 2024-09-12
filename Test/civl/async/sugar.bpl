// Boogie program verifier version 3.2.0.0, Copyright (c) 2003-2014, Microsoft.
// Command Line Options: 2pc.bpl /civlDesugaredFile:sugar.bpl /keepQuantifier

type Xid = int;

type Mid = int;

const CoordinatorMid: int;

function coordinatorMid(mid: int) : bool
uses {
axiom (forall mid: int :: 
  { coordinatorMid(mid) } 
  coordinatorMid(mid) <==> mid == CoordinatorMid);
}

const numParticipants: int;

function participantMid(mid: int) : bool
uses {
axiom (forall mid: int :: 
  { participantMid(mid) } 
  participantMid(mid) <==> 1 <= mid && mid <= numParticipants);
}

datatype Pair {
  Pair(xid: int, mid: int)
}

function {:inline} pair(xid: int, mid: int, p: Pair) : bool
{
  p == Pair(xid, mid) && participantMid(p->mid)
}

function {:inline} perm(xid: int) : Set_5714
{
  Set_5714((lambda p: Pair :: pair(xid, p->mid, p)))
}

type MState = int;

function {:inline} ABORTED() : int
{
  0
}

function {:inline} UNDECIDED() : int
{
  1
}

function {:inline} COMMITTED() : int
{
  2
}

function {:inline} Aborted(i: int) : bool
{
  i == ABORTED()
}

function {:inline} Undecided(i: int) : bool
{
  i == UNDECIDED()
}

function {:inline} Committed(i: int) : bool
{
  i == COMMITTED()
}

function {:inline} UndecidedOrAborted(i: int) : bool
{
  Undecided(i) || Aborted(i)
}

function {:inline} UndecidedOrCommitted(i: int) : bool
{
  Undecided(i) || Committed(i)
}

type XState = [int]int;

type GState = [int][int]int;

var state: [int][int]int;

var votes: [int]int;

var B: Set_5714;

var UnallocatedXids: Set_5714;

function {:inline} xUndecided(state: [int]int) : bool
{
  Undecided(state[CoordinatorMid])
     && (forall i: int :: participantMid(i) ==> Undecided(state[i]))
}

function {:inline} xUndecidedOrCommitted(state: [int]int) : bool
{
  UndecidedOrCommitted(state[CoordinatorMid])
     && (forall i: int :: participantMid(i) ==> UndecidedOrCommitted(state[i]))
}

function {:inline} xUndecidedOrAborted(state: [int]int) : bool
{
  UndecidedOrAborted(state[CoordinatorMid])
     && (forall i: int :: participantMid(i) ==> UndecidedOrAborted(state[i]))
}

function {:inline} xConsistent(state: [int]int) : bool
{
  xUndecidedOrCommitted(state) || xUndecidedOrAborted(state)
}

function {:inline} xNoUndoneDecision(oldState: [int]int, newState: [int]int) : bool
{
  (newState[CoordinatorMid] == oldState[CoordinatorMid]
       || Undecided(oldState[CoordinatorMid]))
     && (forall i: int :: 
      participantMid(i) ==> newState[i] == oldState[i] || Undecided(oldState[i]))
}

function {:inline} xConsistentExtension(oldState: [int]int, newState: [int]int) : bool
{
  xConsistent(newState) && xNoUndoneDecision(oldState, newState)
}

function {:inline} xAllParticipantsInB(xid: int, B: Set_5714) : bool
{
  (forall mid: int :: 
    participantMid(mid) ==> Set_Contains_4605(B, Pair(xid, mid)))
}

function {:inline} gUndecided(state: [int][int]int) : bool
{
  (forall j: int :: xUndecided(state[j]))
}

function {:inline} gConsistent(state: [int][int]int) : bool
{
  (forall j: int :: xConsistent(state[j]))
}

function {:inline} ExistsMonotoneExtension(snapshot: [int][int]int, state: [int][int]int, xid: int) : bool
{
  (exists newState: [int]int :: 
    state == snapshot[xid := newState] && xNoUndoneDecision(snapshot[xid], newState))
}

function {:inline} VotesEqCoordinatorState(votes: [int]int, state: [int][int]int, xid: int) : bool
{
  (votes[xid] == -1 <==> Aborted(state[xid][CoordinatorMid]))
     && (0 <= votes[xid] && votes[xid] < numParticipants
       <==> Undecided(state[xid][CoordinatorMid]))
     && (votes[xid] == numParticipants <==> Committed(state[xid][CoordinatorMid]))
}

function {:inline} SetInv(B: [Pair]bool) : bool
{
  (forall xid: int, mid: int :: B[Pair(xid, mid)] ==> participantMid(mid))
}

function {:inline} Inv_8(state: [int][int]int, B: Set_5714, votes: [int]int) : bool
{
  gConsistent(state)
     && SetInv(B->val)
     && (forall xid: int :: VotesEqCoordinatorState(votes, state, xid))
     && (forall xid: int :: votes[xid] == -1 || votes[xid] == card(B->val, xid))
     && (forall p: Pair :: 
      Set_Contains_4605(B, p) && votes[p->xid] != -1
         ==> UndecidedOrCommitted(state[p->xid][p->mid]))
}

function {:inline} Inv_9(state: [int][int]int, B: Set_5714, xid: int) : bool
{
  gConsistent(state)
     && (xAllParticipantsInB(xid, B) || xUndecidedOrAborted(state[xid]))
}

function card(pairs: [Pair]bool, xid: int) : int;

pure procedure Lemma_add_to_set(set: [Pair]bool, pair: Pair);
  requires participantMid(pair->mid);
  requires !set[pair];
  ensures (forall xid: int :: 
    card(set[pair := true], xid)
       == (if xid == pair->xid then card(set, xid) + 1 else card(set, xid)));



pure procedure Lemma_all_in_set(set: [Pair]bool, xid: int);
  requires SetInv(set);
  ensures card(set, xid) >= numParticipants
     ==> (forall mid: int :: participantMid(mid) ==> set[Pair(xid, mid)]);



const Identity: [int]int;

function {:inline} AtLeast(x: int) : [int]bool
{
  MapLe_2744(MapConst_2761_2744(x), Identity)
}

function {:inline} Range(from: int, n: int) : [int]bool
{
  MapDiff_2764(AtLeast(from), AtLeast(from + n))
}

type {:builtin "Seq"} Seq _;

pure procedure Assume(b: bool);
  ensures b;



datatype Set_5714 {
  Set_5714(val: [Pair]bool)
}

function {:inline} Set_Contains_4605(a: Set_5714, t: Pair) : bool
{
  a->val[t]
}

datatype One_6657 {
  One_6657(val: Pair)
}

pure procedure {:inline 1} Copy_7021(v: [int][int]int) returns (copy_v: [int][int]int);



implementation {:inline 1} Copy_7021(v: [int][int]int) returns (copy_v: [int][int]int)
{

  anon0:
    copy_v := v;
    return;
}



pure procedure One_Get_4654(path: Set_5714, k: Pair) returns (l: One_6657);



function {:inline} Set_IsDisjoint_4577(a: Set_5714, b: Set_5714) : bool
{
  Set_Intersection_4577(a, b) == Set_Empty_4577()
}

function {:inline} Set_Intersection_4577(a: Set_5714, b: Set_5714) : Set_5714
{
  Set_5714(MapAnd_4577(a->val, b->val))
}

function {:builtin "MapAnd"} MapAnd_4577([Pair]bool, [Pair]bool) : [Pair]bool;

function {:inline} Set_Empty_4577() : Set_5714
{
  Set_5714(MapConst_5_4577(false))
}

function {:builtin "MapConst"} MapConst_5_4577(bool) : [Pair]bool;

pure procedure One_Put_4588(path: Set_5714, l: One_6657);



function {:inline} Set_IsSubset_4812(a: Set_5714, b: Set_5714) : bool
{
  IsSubset_4812(a->val, b->val)
}

function {:inline} IsSubset_4812(a: [Pair]bool, b: [Pair]bool) : bool
{
  MapImp_4812(a, b) == MapConst_5_4577(true)
}

function {:builtin "MapImp"} MapImp_4812([Pair]bool, [Pair]bool) : [Pair]bool;

pure procedure Set_Split_4590(path: Set_5714, l: Set_5714);



function {:builtin "MapConst"} MapConst_2761_2744(int) : [int]int;

function {:builtin "MapLe"} MapLe_2744([int]int, [int]int) : [int]bool;

function {:inline} MapDiff_2764(a: [int]bool, b: [int]bool) : [int]bool
{
  MapAnd_2764(a, MapNot_2764(b))
}

function {:builtin "MapNot"} MapNot_2764([int]bool) : [int]bool;

function {:builtin "MapAnd"} MapAnd_2764([int]bool, [int]bool) : [int]bool;

datatype Vec_5 {
  Vec_5(contents: [int]bool, len: int)
}

function Default_5() : bool;

function {:builtin "MapConst"} MapConst_5_2785(bool) : [int]bool;

function {:builtin "MapIte"} MapIte_2785_5([int]bool, [int]bool, [int]bool) : [int]bool;

datatype Vec_2761 {
  Vec_2761(contents: [int]int, len: int)
}

function Default_2761() : int;

function {:builtin "MapIte"} MapIte_2785_2761([int]bool, [int]int, [int]int) : [int]int;

function Choice_4577(a: [Pair]bool) : Pair;

function Choice_2744(a: [int]bool) : int;

axiom CoordinatorMid == 0;

axiom 0 < numParticipants;

axiom (forall x: int :: Identity[x] == x);

axiom (forall x: Vec_2761 :: 
  { x->len } { x->contents } 
  MapIte_2785_2761(Range(0, x->len), MapConst_2761_2744(Default_2761()), x->contents)
     == MapConst_2761_2744(Default_2761()));

axiom (forall x: Vec_5 :: 
  { x->len } { x->contents } 
  MapIte_2785_5(Range(0, x->len), MapConst_5_2785(Default_5()), x->contents)
     == MapConst_5_2785(Default_5()));

axiom (forall x: Vec_2761 :: { x->len } x->len >= 0);

axiom (forall x: Vec_5 :: { x->len } x->len >= 0);

axiom (forall a: [int]bool :: 
  { Choice_2744(a) } 
  a == MapConst_5_2785(false) || a[Choice_2744(a)]);

axiom (forall a: [Pair]bool :: 
  { Choice_4577(a) } 
  a == MapConst_5_4577(false) || a[Choice_4577(a)]);

function {:builtin "MapConst"} MapConst_3_5714(int) : [Pair]int;

function {:builtin "MapOr"} MapOr_5714([Pair]bool, [Pair]bool) : [Pair]bool;

function {:builtin "MapEq"} MapEq_5714_3([Pair]int, [Pair]int) : [Pair]bool;

function {:builtin "MapAdd"} MapAdd_5714([Pair]int, [Pair]int) : [Pair]int;

function {:builtin "MapIte"} MapIte_5714_3([Pair]bool, [Pair]int, [Pair]int) : [Pair]int;

function {:builtin "MapLe"} MapLe_5714([Pair]int, [Pair]int) : [Pair]bool;

function {:inline} Set_Collector_5714(a: Set_5714) : [Pair]bool
{
  a->val
}

function {:inline} One_Collector_6657(a: One_6657) : [Pair]bool
{
  MapOne_6657(a->val)
}

function {:inline} MapOne_6657(t: Pair) : [Pair]bool
{
  MapConst_5_4577(false)[t := true]
}

function {:inline} Set_Add_4588(a: Set_5714, t: Pair) : Set_5714
{
  Set_5714(a->val[t := true])
}

function {:inline} Set_Difference_4590(a: Set_5714, b: Set_5714) : Set_5714
{
  Set_5714(MapDiff_4590(a->val, b->val))
}

function {:inline} MapDiff_4590(a: [Pair]bool, b: [Pair]bool) : [Pair]bool
{
  MapAnd_4577(a, MapNot_4590(b))
}

function {:builtin "MapNot"} MapNot_4590([Pair]bool) : [Pair]bool;

function {:inline} Set_Remove_4654(a: Set_5714, t: Pair) : Set_5714
{
  Set_5714(a->val[t := false])
}

function Trigger_atomic_Coordinator_TransactionReq_x(x: [int]int) : bool;

function Trigger_atomic_Participant_VoteReq_x(x: [int]int) : bool;

function Trigger_atomic_Coordinator_VoteYes_x(x: [int]int) : bool;

function Trigger_atomic_Coordinator_VoteNo_x(x: [int]int) : bool;

implementation atomic_Coordinator_TransactionReq() returns (xid: int)
{
  var {:pool "A"} x: [int]int;

  /*** structured program:
    state[xid] := x;
    assume xConsistent(state[xid]);
  **** end structured program */

  anon0:
    assume Trigger_atomic_Coordinator_TransactionReq_x(x);
    state[xid] := x;
    assume xConsistent(state[xid]);
    return;
}



procedure {:inline 1} atomic_Coordinator_TransactionReq() returns (xid: int);
  modifies state;



function {:inline} Civl_InputOutputRelation_atomic_Coordinator_TransactionReq(xid: int) : bool
{
  (exists Civl_old_state: [int][int]int, 
      Civl_old_votes: [int]int, 
      Civl_old_B: Set_5714, 
      Civl_old_UnallocatedXids: Set_5714, 
      Civl_state: [int][int]int, 
      Civl_votes: [int]int, 
      Civl_B: Set_5714, 
      Civl_UnallocatedXids: Set_5714, 
      {:pool "A"} Civl_x#0: [int]int :: 
    xConsistent(Civl_state[xid]) && Civl_state == Civl_old_state[xid := Civl_x#0])
}

implementation atomic_Participant_VoteReq(xid: int, mid: int, pair: One_6657)
{
  var {:pool "A"} x: [int]int;

  /*** structured program:
    assert Set_IsDisjoint_4577(perm(xid), UnallocatedXids);
    assert pair(xid, mid, pair->val);
    assert xConsistent(state[xid]);
    state[xid] := x;
    assume xConsistentExtension(old(state)[xid], state[xid]);
  **** end structured program */

  anon0:
    assume Trigger_atomic_Participant_VoteReq_x(x);
    state[xid] := x;
    assume xConsistentExtension(old(state)[xid], state[xid]);
    return;
}



procedure {:inline 1} atomic_Participant_VoteReq(xid: int, mid: int, pair: One_6657);
  modifies state;



function {:inline} Civl_InputOutputRelation_atomic_Participant_VoteReq(xid: int, mid: int, pair: One_6657) : bool
{
  (exists Civl_old_state: [int][int]int, 
      Civl_old_votes: [int]int, 
      Civl_old_B: Set_5714, 
      Civl_old_UnallocatedXids: Set_5714, 
      Civl_state: [int][int]int, 
      Civl_votes: [int]int, 
      Civl_B: Set_5714, 
      Civl_UnallocatedXids: Set_5714 :: 
    xConsistent(Civl_old_state[xid])
       && pair(xid, mid, pair->val)
       && Set_IsDisjoint_4577(perm(xid), Civl_old_UnallocatedXids)
       && (exists {:pool "A"} Civl_x#0: [int]int :: 
        xConsistentExtension(Civl_old_state[xid], Civl_state[xid])
           && Civl_state == Civl_old_state[xid := Civl_x#0]))
}

implementation atomic_Coordinator_VoteYes(xid: int, mid: int, pair: One_6657)
{
  var {:pool "A"} x: [int]int;

  /*** structured program:
    assert Set_IsDisjoint_4577(perm(xid), UnallocatedXids);
    assert pair(xid, mid, pair->val);
    assert xConsistent(state[xid]);
    call One_Put_4588(B, pair);
    if (*)
    {
        state[xid] := x;
        assume xAllParticipantsInB(xid, B);
        assume xConsistentExtension(old(state)[xid], state[xid]);
    }
  **** end structured program */

  anon0:
    assume Trigger_atomic_Coordinator_VoteYes_x(x);
    B := Set_Add_4588(B, pair->val);
    goto anon2_Then, anon2_Else;

  anon2_Else:
    return;

  anon2_Then:
    state[xid] := x;
    assume xAllParticipantsInB(xid, B);
    assume xConsistentExtension(old(state)[xid], state[xid]);
    return;
}



procedure {:inline 1} atomic_Coordinator_VoteYes(xid: int, mid: int, pair: One_6657);
  modifies state, B;



function {:inline} Civl_InputOutputRelation_atomic_Coordinator_VoteYes(xid: int, mid: int, pair: One_6657) : bool
{
  (exists Civl_old_state: [int][int]int, 
      Civl_old_votes: [int]int, 
      Civl_old_B: Set_5714, 
      Civl_old_UnallocatedXids: Set_5714, 
      Civl_state: [int][int]int, 
      Civl_votes: [int]int, 
      Civl_B: Set_5714, 
      Civl_UnallocatedXids: Set_5714 :: 
    xConsistent(Civl_old_state[xid])
       && pair(xid, mid, pair->val)
       && Set_IsDisjoint_4577(perm(xid), Civl_old_UnallocatedXids)
       && ((exists {:pool "A"} Civl_x#0: [int]int :: 
          xAllParticipantsInB(xid, Civl_B)
             && xConsistentExtension(Civl_old_state[xid], Civl_state[xid])
             && Civl_B == Set_Add_4588(Civl_old_B, pair->val)
             && Civl_state == Civl_old_state[xid := Civl_x#0])
         || (Civl_B == Set_Add_4588(Civl_old_B, pair->val) && Civl_state == Civl_old_state)))
}

implementation atomic_Coordinator_VoteNo(xid: int, mid: int, pair: One_6657)
{
  var {:pool "A"} x: [int]int;

  /*** structured program:
    assert Set_IsDisjoint_4577(perm(xid), UnallocatedXids);
    assert pair(xid, mid, pair->val);
    assert xUndecidedOrAborted(state[xid]);
    state[xid] := x;
    assume xUndecidedOrAborted(state[xid]);
    assume xConsistentExtension(old(state)[xid], state[xid]);
  **** end structured program */

  anon0:
    assume Trigger_atomic_Coordinator_VoteNo_x(x);
    state[xid] := x;
    assume xUndecidedOrAborted(state[xid]);
    assume xConsistentExtension(old(state)[xid], state[xid]);
    return;
}



procedure {:inline 1} atomic_Coordinator_VoteNo(xid: int, mid: int, pair: One_6657);
  modifies state;



function {:inline} Civl_InputOutputRelation_atomic_Coordinator_VoteNo(xid: int, mid: int, pair: One_6657) : bool
{
  (exists Civl_old_state: [int][int]int, 
      Civl_old_votes: [int]int, 
      Civl_old_B: Set_5714, 
      Civl_old_UnallocatedXids: Set_5714, 
      Civl_state: [int][int]int, 
      Civl_votes: [int]int, 
      Civl_B: Set_5714, 
      Civl_UnallocatedXids: Set_5714 :: 
    xUndecidedOrAborted(Civl_old_state[xid])
       && pair(xid, mid, pair->val)
       && Set_IsDisjoint_4577(perm(xid), Civl_old_UnallocatedXids)
       && (exists {:pool "A"} Civl_x#0: [int]int :: 
        xUndecidedOrAborted(Civl_state[xid])
           && xConsistentExtension(Civl_old_state[xid], Civl_state[xid])
           && Civl_state == Civl_old_state[xid := Civl_x#0]))
}

implementation atomic_SetParticipantAborted(xid: int, mid: int, pair: One_6657)
{
  /*** structured program:
    assert pair(xid, mid, pair->val);
    assert xUndecidedOrAborted(state[xid]);
    state[xid][mid] := ABORTED();
  **** end structured program */

  anon0:
    state[xid][mid] := ABORTED();
    return;
}



procedure {:inline 1} atomic_SetParticipantAborted(xid: int, mid: int, pair: One_6657);
  modifies state;



function {:inline} Civl_InputOutputRelation_atomic_SetParticipantAborted(xid: int, mid: int, pair: One_6657) : bool
{
  (exists Civl_old_state: [int][int]int, 
      Civl_old_votes: [int]int, 
      Civl_old_B: Set_5714, 
      Civl_old_UnallocatedXids: Set_5714, 
      Civl_state: [int][int]int, 
      Civl_votes: [int]int, 
      Civl_B: Set_5714, 
      Civl_UnallocatedXids: Set_5714 :: 
    xUndecidedOrAborted(Civl_old_state[xid])
       && pair(xid, mid, pair->val)
       && Civl_state == Civl_old_state[xid := Civl_old_state[xid][mid := ABORTED()]])
}

implementation atomic_StateUpdateOnVoteYes(xid: int, mid: int, pair: One_6657) returns (commit: bool)
{
  /*** structured program:
    assert Set_IsDisjoint_4577(perm(xid), UnallocatedXids);
    assert VotesEqCoordinatorState(votes, state, xid);
    call One_Put_4588(B, pair);
    if (votes[xid] == -1)
    {
        commit := false;
    }
    else
    {
        votes[xid] := votes[xid] + 1;
        commit := votes[xid] == numParticipants;
        state[xid][CoordinatorMid] := (if commit then COMMITTED() else state[xid][CoordinatorMid]);
    }
  **** end structured program */

  anon0:
    B := Set_Add_4588(B, pair->val);
    goto anon3_Then, anon3_Else;

  anon3_Else:
    assume {:partition} votes[xid] != -1;
    votes[xid] := votes[xid] + 1;
    commit := votes[xid] == numParticipants;
    state[xid][CoordinatorMid] := (if commit then COMMITTED() else state[xid][CoordinatorMid]);
    return;

  anon3_Then:
    assume {:partition} votes[xid] == -1;
    commit := false;
    return;
}



procedure {:inline 1} atomic_StateUpdateOnVoteYes(xid: int, mid: int, pair: One_6657) returns (commit: bool);
  modifies votes, state, B;



function {:inline} Civl_InputOutputRelation_atomic_StateUpdateOnVoteYes(xid: int, mid: int, pair: One_6657, commit: bool) : bool
{
  (exists Civl_old_state: [int][int]int, 
      Civl_old_votes: [int]int, 
      Civl_old_B: Set_5714, 
      Civl_old_UnallocatedXids: Set_5714, 
      Civl_state: [int][int]int, 
      Civl_votes: [int]int, 
      Civl_B: Set_5714, 
      Civl_UnallocatedXids: Set_5714 :: 
    VotesEqCoordinatorState(Civl_old_votes, Civl_old_state, xid)
       && Set_IsDisjoint_4577(perm(xid), Civl_old_UnallocatedXids)
       && ((
          Civl_votes[xid] == -1
           && Civl_B == Set_Add_4588(Civl_old_B, pair->val)
           && (commit <==> false)
           && Civl_votes == Civl_old_votes
           && Civl_state == Civl_old_state)
         || (
          Civl_old_votes[xid] != -1
           && Civl_B == Set_Add_4588(Civl_old_B, pair->val)
           && Civl_votes == Civl_old_votes[xid := Civl_old_votes[xid] + 1]
           && (commit <==> Civl_votes[xid] == numParticipants)
           && Civl_state
             == Civl_old_state[xid := Civl_old_state[xid][CoordinatorMid := (if commit then COMMITTED() else Civl_old_state[xid][CoordinatorMid])]])))
}

implementation atomic_StateUpdateOnVoteNo(xid: int, mid: int) returns (abort: bool)
{
  /*** structured program:
    assert Set_IsDisjoint_4577(perm(xid), UnallocatedXids);
    assert !Committed(state[xid][CoordinatorMid]);
    abort := votes[xid] != -1;
    votes[xid] := -1;
    state[xid][CoordinatorMid] := (if abort then ABORTED() else state[xid][CoordinatorMid]);
  **** end structured program */

  anon0:
    abort := votes[xid] != -1;
    votes[xid] := -1;
    state[xid][CoordinatorMid] := (if abort then ABORTED() else state[xid][CoordinatorMid]);
    return;
}



procedure {:inline 1} atomic_StateUpdateOnVoteNo(xid: int, mid: int) returns (abort: bool);
  modifies votes, state;



function {:inline} Civl_InputOutputRelation_atomic_StateUpdateOnVoteNo(xid: int, mid: int, abort: bool) : bool
{
  (exists Civl_old_state: [int][int]int, 
      Civl_old_votes: [int]int, 
      Civl_old_B: Set_5714, 
      Civl_old_UnallocatedXids: Set_5714, 
      Civl_state: [int][int]int, 
      Civl_votes: [int]int, 
      Civl_B: Set_5714, 
      Civl_UnallocatedXids: Set_5714 :: 
    !Committed(Civl_old_state[xid][CoordinatorMid])
       && Set_IsDisjoint_4577(perm(xid), Civl_old_UnallocatedXids)
       && 
      (abort <==> Civl_old_votes[xid] != -1)
       && Civl_votes == Civl_old_votes[xid := -1]
       && Civl_state
         == Civl_old_state[xid := Civl_old_state[xid][CoordinatorMid := (if abort then ABORTED() else Civl_old_state[xid][CoordinatorMid])]])
}

implementation atomic_Participant_Commit(xid: int, mid: int)
{
  /*** structured program:
    assert participantMid(mid);
    assert xUndecidedOrCommitted(state[xid]);
    assert Committed(state[xid][CoordinatorMid]);
    state[xid][mid] := COMMITTED();
  **** end structured program */

  anon0:
    state[xid][mid] := COMMITTED();
    return;
}



procedure {:inline 1} atomic_Participant_Commit(xid: int, mid: int);
  modifies state;



function {:inline} Civl_InputOutputRelation_atomic_Participant_Commit(xid: int, mid: int) : bool
{
  (exists Civl_old_state: [int][int]int, 
      Civl_old_votes: [int]int, 
      Civl_old_B: Set_5714, 
      Civl_old_UnallocatedXids: Set_5714, 
      Civl_state: [int][int]int, 
      Civl_votes: [int]int, 
      Civl_B: Set_5714, 
      Civl_UnallocatedXids: Set_5714 :: 
    Committed(Civl_old_state[xid][CoordinatorMid])
       && xUndecidedOrCommitted(Civl_old_state[xid])
       && participantMid(mid)
       && Civl_state == Civl_old_state[xid := Civl_old_state[xid][mid := COMMITTED()]])
}

implementation atomic_Participant_Abort(xid: int, mid: int)
{
  /*** structured program:
    assert participantMid(mid);
    assert xUndecidedOrAborted(state[xid]);
    assert Aborted(state[xid][CoordinatorMid]);
    state[xid][mid] := ABORTED();
  **** end structured program */

  anon0:
    state[xid][mid] := ABORTED();
    return;
}



procedure {:inline 1} atomic_Participant_Abort(xid: int, mid: int);
  modifies state;



function {:inline} Civl_InputOutputRelation_atomic_Participant_Abort(xid: int, mid: int) : bool
{
  (exists Civl_old_state: [int][int]int, 
      Civl_old_votes: [int]int, 
      Civl_old_B: Set_5714, 
      Civl_old_UnallocatedXids: Set_5714, 
      Civl_state: [int][int]int, 
      Civl_votes: [int]int, 
      Civl_B: Set_5714, 
      Civl_UnallocatedXids: Set_5714 :: 
    Aborted(Civl_old_state[xid][CoordinatorMid])
       && xUndecidedOrAborted(Civl_old_state[xid])
       && participantMid(mid)
       && Civl_state == Civl_old_state[xid := Civl_old_state[xid][mid := ABORTED()]])
}

implementation atomic_AllocateXid() returns (xid: int, pairs: Set_5714)
{
  /*** structured program:
    assume state[xid] == (lambda j: int :: UNDECIDED());
    pairs := perm(xid);
    assume Set_IsSubset_4812(pairs, UnallocatedXids);
    call Set_Split_4590(UnallocatedXids, pairs);
  **** end structured program */

  anon0:
    assume state[xid] == (lambda j: int :: UNDECIDED());
    pairs := perm(xid);
    assume Set_IsSubset_4812(pairs, UnallocatedXids);
    UnallocatedXids := Set_Difference_4590(UnallocatedXids, pairs);
    return;
}



procedure {:inline 1} atomic_AllocateXid() returns (xid: int, pairs: Set_5714);
  modifies UnallocatedXids;



function {:inline} Civl_InputOutputRelation_atomic_AllocateXid(xid: int, pairs: Set_5714) : bool
{
  (exists Civl_old_state: [int][int]int, 
      Civl_old_votes: [int]int, 
      Civl_old_B: Set_5714, 
      Civl_old_UnallocatedXids: Set_5714, 
      Civl_state: [int][int]int, 
      Civl_votes: [int]int, 
      Civl_B: Set_5714, 
      Civl_UnallocatedXids: Set_5714 :: 
    (forall xid: int :: 
        Civl_old_state[xid] == (lambda j: int :: UNDECIDED())
           ==> 
          Set_IsSubset_4812(perm(xid), Civl_old_UnallocatedXids)
           ==> Set_IsSubset_4812(perm(xid), Civl_old_UnallocatedXids))
       && 
      Civl_state[xid] == (lambda j: int :: UNDECIDED())
       && Set_IsSubset_4812(pairs, Civl_old_UnallocatedXids)
       && pairs == perm(xid)
       && Civl_UnallocatedXids == Set_Difference_4590(Civl_old_UnallocatedXids, pairs))
}

implementation Civl_Skip()
{

  init:
    return;
}



pure procedure {:inline 1} Civl_Skip();



function {:inline} Civl_InputOutputRelation_Civl_Skip() : bool
{
  (exists Civl_old_state: [int][int]int, 
      Civl_old_votes: [int]int, 
      Civl_old_B: Set_5714, 
      Civl_old_UnallocatedXids: Set_5714, 
      Civl_state: [int][int]int, 
      Civl_votes: [int]int, 
      Civl_B: Set_5714, 
      Civl_UnallocatedXids: Set_5714 :: 
    true)
}

implementation Civl_CommutativityChecker_atomic_Participant_VoteReq_atomic_Participant_VoteReq(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657)
{

  init:
    call atomic_Participant_VoteReq(first_xid, first_mid, first_pair);
    call atomic_Participant_VoteReq(second_xid, second_mid, second_pair);
    assert true
       ==> (exists {:pool "A"} Civl_second_x#0: [int]int, {:pool "A"} Civl_first_x#0: [int]int :: 
        { Trigger_atomic_Participant_VoteReq_x(Civl_second_x#0), Trigger_atomic_Participant_VoteReq_x(Civl_first_x#0) } 
        xConsistentExtension(old(state)[second_xid], old(state)[second_xid := Civl_second_x#0][second_xid])
           && xConsistentExtension(old(state)[second_xid := Civl_second_x#0][first_xid], state[first_xid])
           && state == old(state)[second_xid := Civl_second_x#0][first_xid := Civl_first_x#0]
           && UnallocatedXids == old(UnallocatedXids));
    return;
}



procedure Civl_CommutativityChecker_atomic_Participant_VoteReq_atomic_Participant_VoteReq(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(first_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(One_Collector_6657(second_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
         == MapConst_5_4577(true));
  requires xConsistent(state[first_xid]);
  requires pair(first_xid, first_mid, first_pair->val);
  requires Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids);
  requires xConsistent(state[second_xid]);
  requires pair(second_xid, second_mid, second_pair->val);
  requires Set_IsDisjoint_4577(perm(second_xid), UnallocatedXids);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_GatePreservationChecker_atomic_Participant_VoteReq_atomic_Participant_VoteReq(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657)
{

  init:
    call atomic_Participant_VoteReq(second_xid, second_mid, second_pair);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true))
       ==> xConsistent(state[first_xid]);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true))
       ==> pair(first_xid, first_mid, first_pair->val);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true))
       ==> Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids);
    return;
}



procedure Civl_GatePreservationChecker_atomic_Participant_VoteReq_atomic_Participant_VoteReq(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(first_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(One_Collector_6657(second_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
         == MapConst_5_4577(true));
  requires xConsistent(state[first_xid]);
  requires pair(first_xid, first_mid, first_pair->val);
  requires Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids);
  requires xConsistent(state[second_xid]);
  requires pair(second_xid, second_mid, second_pair->val);
  requires Set_IsDisjoint_4577(perm(second_xid), UnallocatedXids);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_FailurePreservationChecker_atomic_Participant_VoteReq_atomic_Participant_VoteReq(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657)
{

  init:
    call atomic_Participant_VoteReq(second_xid, second_mid, second_pair);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true))
       ==> !(
        xConsistent(state[first_xid])
         && pair(first_xid, first_mid, first_pair->val)
         && Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids));
    return;
}



procedure Civl_FailurePreservationChecker_atomic_Participant_VoteReq_atomic_Participant_VoteReq(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(first_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(One_Collector_6657(second_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
         == MapConst_5_4577(true));
  requires !(
    xConsistent(state[first_xid])
     && pair(first_xid, first_mid, first_pair->val)
     && Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids));
  requires xConsistent(state[second_xid]);
  requires pair(second_xid, second_mid, second_pair->val);
  requires Set_IsDisjoint_4577(perm(second_xid), UnallocatedXids);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_CommutativityChecker_atomic_Coordinator_VoteYes_atomic_Coordinator_VoteYes(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657)
{

  init:
    call atomic_Coordinator_VoteYes(first_xid, first_mid, first_pair);
    call atomic_Coordinator_VoteYes(second_xid, second_mid, second_pair);
    assert (exists Civl_partition_Pair: [Pair]int :: 
          MapImp_4812(Set_Collector_5714(UnallocatedXids), 
                MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
               == MapConst_5_4577(true)
             && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
               == MapConst_5_4577(true))
         && (exists Civl_partition_Pair: [Pair]int :: 
          MapImp_4812(Set_Collector_5714(UnallocatedXids), 
                MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
               == MapConst_5_4577(true)
             && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
               == MapConst_5_4577(true))
       ==> (exists {:pool "A"} Civl_second_x#0: [int]int, {:pool "A"} Civl_first_x#0: [int]int :: 
          { Trigger_atomic_Coordinator_VoteYes_x(Civl_second_x#0), Trigger_atomic_Coordinator_VoteYes_x(Civl_first_x#0) } 
          xAllParticipantsInB(second_xid, Set_Add_4588(old(B), second_pair->val))
             && xConsistentExtension(old(state)[second_xid], old(state)[second_xid := Civl_second_x#0][second_xid])
             && xAllParticipantsInB(first_xid, B)
             && xConsistentExtension(old(state)[second_xid := Civl_second_x#0][first_xid], state[first_xid])
             && B == Set_Add_4588(Set_Add_4588(old(B), second_pair->val), first_pair->val)
             && state == old(state)[second_xid := Civl_second_x#0][first_xid := Civl_first_x#0]
             && UnallocatedXids == old(UnallocatedXids))
         || (exists {:pool "A"} Civl_second_x#0: [int]int :: 
          { Trigger_atomic_Coordinator_VoteYes_x(Civl_second_x#0) } 
          xAllParticipantsInB(second_xid, Set_Add_4588(old(B), second_pair->val))
             && xConsistentExtension(old(state)[second_xid], state[second_xid])
             && state == old(state)[second_xid := Civl_second_x#0]
             && B == Set_Add_4588(Set_Add_4588(old(B), second_pair->val), first_pair->val)
             && UnallocatedXids == old(UnallocatedXids))
         || (exists {:pool "A"} Civl_first_x#0: [int]int :: 
          { Trigger_atomic_Coordinator_VoteYes_x(Civl_first_x#0) } 
          xAllParticipantsInB(first_xid, B)
             && xConsistentExtension(old(state)[first_xid], state[first_xid])
             && B == Set_Add_4588(Set_Add_4588(old(B), second_pair->val), first_pair->val)
             && state == old(state)[first_xid := Civl_first_x#0]
             && UnallocatedXids == old(UnallocatedXids))
         || (
          B == Set_Add_4588(Set_Add_4588(old(B), second_pair->val), first_pair->val)
           && state == old(state)
           && UnallocatedXids == old(UnallocatedXids));
    return;
}



procedure Civl_CommutativityChecker_atomic_Coordinator_VoteYes_atomic_Coordinator_VoteYes(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(first_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(One_Collector_6657(second_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(3)))
         == MapConst_5_4577(true));
  requires xConsistent(state[first_xid]);
  requires pair(first_xid, first_mid, first_pair->val);
  requires Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids);
  requires xConsistent(state[second_xid]);
  requires pair(second_xid, second_mid, second_pair->val);
  requires Set_IsDisjoint_4577(perm(second_xid), UnallocatedXids);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_GatePreservationChecker_atomic_Coordinator_VoteYes_atomic_Coordinator_VoteYes(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657)
{

  init:
    call atomic_Coordinator_VoteYes(second_xid, second_mid, second_pair);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
             == MapConst_5_4577(true))
       ==> xConsistent(state[first_xid]);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
             == MapConst_5_4577(true))
       ==> pair(first_xid, first_mid, first_pair->val);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
             == MapConst_5_4577(true))
       ==> Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids);
    return;
}



procedure Civl_GatePreservationChecker_atomic_Coordinator_VoteYes_atomic_Coordinator_VoteYes(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(first_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(One_Collector_6657(second_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(3)))
         == MapConst_5_4577(true));
  requires xConsistent(state[first_xid]);
  requires pair(first_xid, first_mid, first_pair->val);
  requires Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids);
  requires xConsistent(state[second_xid]);
  requires pair(second_xid, second_mid, second_pair->val);
  requires Set_IsDisjoint_4577(perm(second_xid), UnallocatedXids);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_FailurePreservationChecker_atomic_Coordinator_VoteYes_atomic_Coordinator_VoteYes(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657)
{

  init:
    call atomic_Coordinator_VoteYes(second_xid, second_mid, second_pair);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
             == MapConst_5_4577(true))
       ==> !(
        xConsistent(state[first_xid])
         && pair(first_xid, first_mid, first_pair->val)
         && Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids));
    return;
}



procedure Civl_FailurePreservationChecker_atomic_Coordinator_VoteYes_atomic_Coordinator_VoteYes(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(first_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(One_Collector_6657(second_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(3)))
         == MapConst_5_4577(true));
  requires !(
    xConsistent(state[first_xid])
     && pair(first_xid, first_mid, first_pair->val)
     && Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids));
  requires xConsistent(state[second_xid]);
  requires pair(second_xid, second_mid, second_pair->val);
  requires Set_IsDisjoint_4577(perm(second_xid), UnallocatedXids);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_CommutativityChecker_atomic_Coordinator_VoteYes_atomic_Coordinator_VoteNo(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657)
{

  init:
    call atomic_Coordinator_VoteYes(first_xid, first_mid, first_pair);
    call atomic_Coordinator_VoteNo(second_xid, second_mid, second_pair);
    assert (exists Civl_partition_Pair: [Pair]int :: 
          MapImp_4812(Set_Collector_5714(UnallocatedXids), 
                MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
               == MapConst_5_4577(true)
             && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
               == MapConst_5_4577(true))
         && (exists Civl_partition_Pair: [Pair]int :: 
          MapImp_4812(Set_Collector_5714(UnallocatedXids), 
                MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
               == MapConst_5_4577(true)
             && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
               == MapConst_5_4577(true))
       ==> (exists {:pool "A"} Civl_second_x#0: [int]int, {:pool "A"} Civl_first_x#0: [int]int :: 
          { Trigger_atomic_Coordinator_VoteNo_x(Civl_second_x#0), Trigger_atomic_Coordinator_VoteYes_x(Civl_first_x#0) } 
          xUndecidedOrAborted(old(state)[second_xid := Civl_second_x#0][second_xid])
             && xConsistentExtension(old(state)[second_xid], old(state)[second_xid := Civl_second_x#0][second_xid])
             && xAllParticipantsInB(first_xid, B)
             && xConsistentExtension(old(state)[second_xid := Civl_second_x#0][first_xid], state[first_xid])
             && B == Set_Add_4588(old(B), first_pair->val)
             && state == old(state)[second_xid := Civl_second_x#0][first_xid := Civl_first_x#0]
             && UnallocatedXids == old(UnallocatedXids))
         || (exists {:pool "A"} Civl_second_x#0: [int]int :: 
          { Trigger_atomic_Coordinator_VoteNo_x(Civl_second_x#0) } 
          xUndecidedOrAborted(state[second_xid])
             && xConsistentExtension(old(state)[second_xid], state[second_xid])
             && state == old(state)[second_xid := Civl_second_x#0]
             && B == Set_Add_4588(old(B), first_pair->val)
             && UnallocatedXids == old(UnallocatedXids));
    return;
}



procedure Civl_CommutativityChecker_atomic_Coordinator_VoteYes_atomic_Coordinator_VoteNo(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(first_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(One_Collector_6657(second_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(3)))
         == MapConst_5_4577(true));
  requires xConsistent(state[first_xid]);
  requires pair(first_xid, first_mid, first_pair->val);
  requires Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids);
  requires xUndecidedOrAborted(state[second_xid]);
  requires pair(second_xid, second_mid, second_pair->val);
  requires Set_IsDisjoint_4577(perm(second_xid), UnallocatedXids);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_GatePreservationChecker_atomic_Coordinator_VoteNo_atomic_Coordinator_VoteYes(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657)
{

  init:
    call atomic_Coordinator_VoteYes(second_xid, second_mid, second_pair);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
             == MapConst_5_4577(true))
       ==> xUndecidedOrAborted(state[first_xid]);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
             == MapConst_5_4577(true))
       ==> pair(first_xid, first_mid, first_pair->val);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
             == MapConst_5_4577(true))
       ==> Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids);
    return;
}



procedure Civl_GatePreservationChecker_atomic_Coordinator_VoteNo_atomic_Coordinator_VoteYes(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(first_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(One_Collector_6657(second_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(3)))
         == MapConst_5_4577(true));
  requires xUndecidedOrAborted(state[first_xid]);
  requires pair(first_xid, first_mid, first_pair->val);
  requires Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids);
  requires xConsistent(state[second_xid]);
  requires pair(second_xid, second_mid, second_pair->val);
  requires Set_IsDisjoint_4577(perm(second_xid), UnallocatedXids);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_FailurePreservationChecker_atomic_Coordinator_VoteYes_atomic_Coordinator_VoteNo(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657)
{

  init:
    call atomic_Coordinator_VoteNo(second_xid, second_mid, second_pair);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true))
       ==> !(
        xConsistent(state[first_xid])
         && pair(first_xid, first_mid, first_pair->val)
         && Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids));
    return;
}



procedure Civl_FailurePreservationChecker_atomic_Coordinator_VoteYes_atomic_Coordinator_VoteNo(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(first_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(One_Collector_6657(second_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
         == MapConst_5_4577(true));
  requires !(
    xConsistent(state[first_xid])
     && pair(first_xid, first_mid, first_pair->val)
     && Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids));
  requires xUndecidedOrAborted(state[second_xid]);
  requires pair(second_xid, second_mid, second_pair->val);
  requires Set_IsDisjoint_4577(perm(second_xid), UnallocatedXids);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_CommutativityChecker_atomic_Coordinator_VoteNo_atomic_Coordinator_VoteYes(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657)
{

  init:
    call atomic_Coordinator_VoteNo(first_xid, first_mid, first_pair);
    call atomic_Coordinator_VoteYes(second_xid, second_mid, second_pair);
    assert (exists Civl_partition_Pair: [Pair]int :: 
          MapImp_4812(Set_Collector_5714(UnallocatedXids), 
                MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
               == MapConst_5_4577(true)
             && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
               == MapConst_5_4577(true))
         && (exists Civl_partition_Pair: [Pair]int :: 
          MapImp_4812(Set_Collector_5714(UnallocatedXids), 
                MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
               == MapConst_5_4577(true)
             && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
               == MapConst_5_4577(true))
       ==> (exists {:pool "A"} Civl_second_x#0: [int]int, {:pool "A"} Civl_first_x#0: [int]int :: 
          { Trigger_atomic_Coordinator_VoteYes_x(Civl_second_x#0), Trigger_atomic_Coordinator_VoteNo_x(Civl_first_x#0) } 
          xAllParticipantsInB(second_xid, B)
             && xConsistentExtension(old(state)[second_xid], old(state)[second_xid := Civl_second_x#0][second_xid])
             && xUndecidedOrAborted(state[first_xid])
             && xConsistentExtension(old(state)[second_xid := Civl_second_x#0][first_xid], state[first_xid])
             && B == Set_Add_4588(old(B), second_pair->val)
             && state == old(state)[second_xid := Civl_second_x#0][first_xid := Civl_first_x#0]
             && UnallocatedXids == old(UnallocatedXids))
         || (exists {:pool "A"} Civl_first_x#0: [int]int :: 
          { Trigger_atomic_Coordinator_VoteNo_x(Civl_first_x#0) } 
          xUndecidedOrAborted(state[first_xid])
             && xConsistentExtension(old(state)[first_xid], state[first_xid])
             && B == Set_Add_4588(old(B), second_pair->val)
             && state == old(state)[first_xid := Civl_first_x#0]
             && UnallocatedXids == old(UnallocatedXids));
    return;
}



procedure Civl_CommutativityChecker_atomic_Coordinator_VoteNo_atomic_Coordinator_VoteYes(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(first_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(One_Collector_6657(second_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(3)))
         == MapConst_5_4577(true));
  requires xUndecidedOrAborted(state[first_xid]);
  requires pair(first_xid, first_mid, first_pair->val);
  requires Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids);
  requires xConsistent(state[second_xid]);
  requires pair(second_xid, second_mid, second_pair->val);
  requires Set_IsDisjoint_4577(perm(second_xid), UnallocatedXids);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_GatePreservationChecker_atomic_Coordinator_VoteYes_atomic_Coordinator_VoteNo(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657)
{

  init:
    call atomic_Coordinator_VoteNo(second_xid, second_mid, second_pair);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true))
       ==> xConsistent(state[first_xid]);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true))
       ==> pair(first_xid, first_mid, first_pair->val);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true))
       ==> Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids);
    return;
}



procedure Civl_GatePreservationChecker_atomic_Coordinator_VoteYes_atomic_Coordinator_VoteNo(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(first_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(One_Collector_6657(second_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
         == MapConst_5_4577(true));
  requires xConsistent(state[first_xid]);
  requires pair(first_xid, first_mid, first_pair->val);
  requires Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids);
  requires xUndecidedOrAborted(state[second_xid]);
  requires pair(second_xid, second_mid, second_pair->val);
  requires Set_IsDisjoint_4577(perm(second_xid), UnallocatedXids);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_FailurePreservationChecker_atomic_Coordinator_VoteNo_atomic_Coordinator_VoteYes(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657)
{

  init:
    call atomic_Coordinator_VoteYes(second_xid, second_mid, second_pair);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
             == MapConst_5_4577(true))
       ==> !(
        xUndecidedOrAborted(state[first_xid])
         && pair(first_xid, first_mid, first_pair->val)
         && Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids));
    return;
}



procedure Civl_FailurePreservationChecker_atomic_Coordinator_VoteNo_atomic_Coordinator_VoteYes(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(first_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(One_Collector_6657(second_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(3)))
         == MapConst_5_4577(true));
  requires !(
    xUndecidedOrAborted(state[first_xid])
     && pair(first_xid, first_mid, first_pair->val)
     && Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids));
  requires xConsistent(state[second_xid]);
  requires pair(second_xid, second_mid, second_pair->val);
  requires Set_IsDisjoint_4577(perm(second_xid), UnallocatedXids);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_CommutativityChecker_atomic_Coordinator_VoteNo_atomic_Coordinator_VoteNo(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657)
{

  init:
    call atomic_Coordinator_VoteNo(first_xid, first_mid, first_pair);
    call atomic_Coordinator_VoteNo(second_xid, second_mid, second_pair);
    assert true
       ==> (exists {:pool "A"} Civl_second_x#0: [int]int, {:pool "A"} Civl_first_x#0: [int]int :: 
        { Trigger_atomic_Coordinator_VoteNo_x(Civl_second_x#0), Trigger_atomic_Coordinator_VoteNo_x(Civl_first_x#0) } 
        xUndecidedOrAborted(old(state)[second_xid := Civl_second_x#0][second_xid])
           && xConsistentExtension(old(state)[second_xid], old(state)[second_xid := Civl_second_x#0][second_xid])
           && xUndecidedOrAborted(state[first_xid])
           && xConsistentExtension(old(state)[second_xid := Civl_second_x#0][first_xid], state[first_xid])
           && state == old(state)[second_xid := Civl_second_x#0][first_xid := Civl_first_x#0]
           && UnallocatedXids == old(UnallocatedXids));
    return;
}



procedure Civl_CommutativityChecker_atomic_Coordinator_VoteNo_atomic_Coordinator_VoteNo(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(first_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(One_Collector_6657(second_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
         == MapConst_5_4577(true));
  requires xUndecidedOrAborted(state[first_xid]);
  requires pair(first_xid, first_mid, first_pair->val);
  requires Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids);
  requires xUndecidedOrAborted(state[second_xid]);
  requires pair(second_xid, second_mid, second_pair->val);
  requires Set_IsDisjoint_4577(perm(second_xid), UnallocatedXids);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_GatePreservationChecker_atomic_Coordinator_VoteNo_atomic_Coordinator_VoteNo(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657)
{

  init:
    call atomic_Coordinator_VoteNo(second_xid, second_mid, second_pair);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true))
       ==> xUndecidedOrAborted(state[first_xid]);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true))
       ==> pair(first_xid, first_mid, first_pair->val);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true))
       ==> Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids);
    return;
}



procedure Civl_GatePreservationChecker_atomic_Coordinator_VoteNo_atomic_Coordinator_VoteNo(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(first_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(One_Collector_6657(second_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
         == MapConst_5_4577(true));
  requires xUndecidedOrAborted(state[first_xid]);
  requires pair(first_xid, first_mid, first_pair->val);
  requires Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids);
  requires xUndecidedOrAborted(state[second_xid]);
  requires pair(second_xid, second_mid, second_pair->val);
  requires Set_IsDisjoint_4577(perm(second_xid), UnallocatedXids);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_FailurePreservationChecker_atomic_Coordinator_VoteNo_atomic_Coordinator_VoteNo(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657)
{

  init:
    call atomic_Coordinator_VoteNo(second_xid, second_mid, second_pair);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true))
       ==> !(
        xUndecidedOrAborted(state[first_xid])
         && pair(first_xid, first_mid, first_pair->val)
         && Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids));
    return;
}



procedure Civl_FailurePreservationChecker_atomic_Coordinator_VoteNo_atomic_Coordinator_VoteNo(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(first_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(One_Collector_6657(second_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
         == MapConst_5_4577(true));
  requires !(
    xUndecidedOrAborted(state[first_xid])
     && pair(first_xid, first_mid, first_pair->val)
     && Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids));
  requires xUndecidedOrAborted(state[second_xid]);
  requires pair(second_xid, second_mid, second_pair->val);
  requires Set_IsDisjoint_4577(perm(second_xid), UnallocatedXids);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_CommutativityChecker_atomic_SetParticipantAborted_atomic_Coordinator_VoteYes(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657)
{

  init:
    call atomic_SetParticipantAborted(first_xid, first_mid, first_pair);
    call atomic_Coordinator_VoteYes(second_xid, second_mid, second_pair);
    assert (exists Civl_partition_Pair: [Pair]int :: 
          MapImp_4812(Set_Collector_5714(UnallocatedXids), 
                MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
               == MapConst_5_4577(true)
             && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
               == MapConst_5_4577(true))
         && (exists Civl_partition_Pair: [Pair]int :: 
          MapImp_4812(Set_Collector_5714(UnallocatedXids), 
                MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
               == MapConst_5_4577(true)
             && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
               == MapConst_5_4577(true))
       ==> (exists {:pool "A"} Civl_second_x#0: [int]int :: 
          { Trigger_atomic_Coordinator_VoteYes_x(Civl_second_x#0) } 
          xAllParticipantsInB(second_xid, B)
             && xConsistentExtension(old(state)[second_xid], old(state)[second_xid := Civl_second_x#0][second_xid])
             && B == Set_Add_4588(old(B), second_pair->val)
             && state
               == old(state)[second_xid := Civl_second_x#0][first_xid := old(state)[second_xid := Civl_second_x#0][first_xid][first_mid := ABORTED()]]
             && UnallocatedXids == old(UnallocatedXids))
         || (
          B == Set_Add_4588(old(B), second_pair->val)
           && state == old(state)[first_xid := old(state)[first_xid][first_mid := ABORTED()]]
           && UnallocatedXids == old(UnallocatedXids));
    return;
}



procedure Civl_CommutativityChecker_atomic_SetParticipantAborted_atomic_Coordinator_VoteYes(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(first_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(One_Collector_6657(second_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(3)))
         == MapConst_5_4577(true));
  requires xUndecidedOrAborted(state[first_xid]);
  requires pair(first_xid, first_mid, first_pair->val);
  requires xConsistent(state[second_xid]);
  requires pair(second_xid, second_mid, second_pair->val);
  requires Set_IsDisjoint_4577(perm(second_xid), UnallocatedXids);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_GatePreservationChecker_atomic_Coordinator_VoteYes_atomic_SetParticipantAborted(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657)
{

  init:
    call atomic_SetParticipantAborted(second_xid, second_mid, second_pair);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true))
       ==> xConsistent(state[first_xid]);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true))
       ==> pair(first_xid, first_mid, first_pair->val);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true))
       ==> Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids);
    return;
}



procedure Civl_GatePreservationChecker_atomic_Coordinator_VoteYes_atomic_SetParticipantAborted(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(first_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(One_Collector_6657(second_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
         == MapConst_5_4577(true));
  requires xConsistent(state[first_xid]);
  requires pair(first_xid, first_mid, first_pair->val);
  requires Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids);
  requires xUndecidedOrAborted(state[second_xid]);
  requires pair(second_xid, second_mid, second_pair->val);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_FailurePreservationChecker_atomic_SetParticipantAborted_atomic_Coordinator_VoteYes(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657)
{

  init:
    call atomic_Coordinator_VoteYes(second_xid, second_mid, second_pair);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
             == MapConst_5_4577(true))
       ==> !(xUndecidedOrAborted(state[first_xid])
         && pair(first_xid, first_mid, first_pair->val));
    return;
}



procedure Civl_FailurePreservationChecker_atomic_SetParticipantAborted_atomic_Coordinator_VoteYes(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(first_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(One_Collector_6657(second_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(3)))
         == MapConst_5_4577(true));
  requires !(xUndecidedOrAborted(state[first_xid])
     && pair(first_xid, first_mid, first_pair->val));
  requires xConsistent(state[second_xid]);
  requires pair(second_xid, second_mid, second_pair->val);
  requires Set_IsDisjoint_4577(perm(second_xid), UnallocatedXids);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_CommutativityChecker_atomic_SetParticipantAborted_atomic_Coordinator_VoteNo(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657)
{

  init:
    call atomic_SetParticipantAborted(first_xid, first_mid, first_pair);
    call atomic_Coordinator_VoteNo(second_xid, second_mid, second_pair);
    assert true
       ==> (exists {:pool "A"} Civl_second_x#0: [int]int :: 
        { Trigger_atomic_Coordinator_VoteNo_x(Civl_second_x#0) } 
        xUndecidedOrAborted(old(state)[second_xid := Civl_second_x#0][second_xid])
           && xConsistentExtension(old(state)[second_xid], old(state)[second_xid := Civl_second_x#0][second_xid])
           && state
             == old(state)[second_xid := Civl_second_x#0][first_xid := old(state)[second_xid := Civl_second_x#0][first_xid][first_mid := ABORTED()]]
           && UnallocatedXids == old(UnallocatedXids));
    return;
}



procedure Civl_CommutativityChecker_atomic_SetParticipantAborted_atomic_Coordinator_VoteNo(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(first_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(One_Collector_6657(second_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
         == MapConst_5_4577(true));
  requires xUndecidedOrAborted(state[first_xid]);
  requires pair(first_xid, first_mid, first_pair->val);
  requires xUndecidedOrAborted(state[second_xid]);
  requires pair(second_xid, second_mid, second_pair->val);
  requires Set_IsDisjoint_4577(perm(second_xid), UnallocatedXids);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_GatePreservationChecker_atomic_Coordinator_VoteNo_atomic_SetParticipantAborted(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657)
{

  init:
    call atomic_SetParticipantAborted(second_xid, second_mid, second_pair);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true))
       ==> xUndecidedOrAborted(state[first_xid]);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true))
       ==> pair(first_xid, first_mid, first_pair->val);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true))
       ==> Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids);
    return;
}



procedure Civl_GatePreservationChecker_atomic_Coordinator_VoteNo_atomic_SetParticipantAborted(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(first_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(One_Collector_6657(second_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
         == MapConst_5_4577(true));
  requires xUndecidedOrAborted(state[first_xid]);
  requires pair(first_xid, first_mid, first_pair->val);
  requires Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids);
  requires xUndecidedOrAborted(state[second_xid]);
  requires pair(second_xid, second_mid, second_pair->val);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_FailurePreservationChecker_atomic_SetParticipantAborted_atomic_Coordinator_VoteNo(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657)
{

  init:
    call atomic_Coordinator_VoteNo(second_xid, second_mid, second_pair);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true))
       ==> !(xUndecidedOrAborted(state[first_xid])
         && pair(first_xid, first_mid, first_pair->val));
    return;
}



procedure Civl_FailurePreservationChecker_atomic_SetParticipantAborted_atomic_Coordinator_VoteNo(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(first_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(One_Collector_6657(second_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
         == MapConst_5_4577(true));
  requires !(xUndecidedOrAborted(state[first_xid])
     && pair(first_xid, first_mid, first_pair->val));
  requires xUndecidedOrAborted(state[second_xid]);
  requires pair(second_xid, second_mid, second_pair->val);
  requires Set_IsDisjoint_4577(perm(second_xid), UnallocatedXids);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_CommutativityChecker_atomic_SetParticipantAborted_atomic_Participant_Commit(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int)
{

  init:
    call atomic_SetParticipantAborted(first_xid, first_mid, first_pair);
    call atomic_Participant_Commit(second_xid, second_mid);
    assert true
       ==> state
         == old(state)[second_xid := old(state)[second_xid][second_mid := COMMITTED()]][first_xid := old(state)[second_xid := old(state)[second_xid][second_mid := COMMITTED()]][first_xid][first_mid := ABORTED()]];
    return;
}



procedure Civl_CommutativityChecker_atomic_SetParticipantAborted_atomic_Participant_Commit(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int);
  requires true;
  requires xUndecidedOrAborted(state[first_xid]);
  requires pair(first_xid, first_mid, first_pair->val);
  requires Committed(state[second_xid][CoordinatorMid]);
  requires xUndecidedOrCommitted(state[second_xid]);
  requires participantMid(second_mid);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_GatePreservationChecker_atomic_Participant_Commit_atomic_SetParticipantAborted(first_xid: int, 
    first_mid: int, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657)
{

  init:
    call atomic_SetParticipantAborted(second_xid, second_mid, second_pair);
    assert true ==> Committed(state[first_xid][CoordinatorMid]);
    assert true ==> xUndecidedOrCommitted(state[first_xid]);
    assert true ==> participantMid(first_mid);
    return;
}



procedure Civl_GatePreservationChecker_atomic_Participant_Commit_atomic_SetParticipantAborted(first_xid: int, 
    first_mid: int, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657);
  requires true;
  requires Committed(state[first_xid][CoordinatorMid]);
  requires xUndecidedOrCommitted(state[first_xid]);
  requires participantMid(first_mid);
  requires xUndecidedOrAborted(state[second_xid]);
  requires pair(second_xid, second_mid, second_pair->val);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_FailurePreservationChecker_atomic_SetParticipantAborted_atomic_Participant_Commit(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int)
{

  init:
    call atomic_Participant_Commit(second_xid, second_mid);
    assert true
       ==> !(xUndecidedOrAborted(state[first_xid])
         && pair(first_xid, first_mid, first_pair->val));
    return;
}



procedure Civl_FailurePreservationChecker_atomic_SetParticipantAborted_atomic_Participant_Commit(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int);
  requires true;
  requires !(xUndecidedOrAborted(state[first_xid])
     && pair(first_xid, first_mid, first_pair->val));
  requires Committed(state[second_xid][CoordinatorMid]);
  requires xUndecidedOrCommitted(state[second_xid]);
  requires participantMid(second_mid);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_CommutativityChecker_atomic_SetParticipantAborted_atomic_Participant_Abort(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int)
{

  init:
    call atomic_SetParticipantAborted(first_xid, first_mid, first_pair);
    call atomic_Participant_Abort(second_xid, second_mid);
    assert true
       ==> state
         == old(state)[second_xid := old(state)[second_xid][second_mid := ABORTED()]][first_xid := old(state)[second_xid := old(state)[second_xid][second_mid := ABORTED()]][first_xid][first_mid := ABORTED()]];
    return;
}



procedure Civl_CommutativityChecker_atomic_SetParticipantAborted_atomic_Participant_Abort(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int);
  requires true;
  requires xUndecidedOrAborted(state[first_xid]);
  requires pair(first_xid, first_mid, first_pair->val);
  requires Aborted(state[second_xid][CoordinatorMid]);
  requires xUndecidedOrAborted(state[second_xid]);
  requires participantMid(second_mid);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_GatePreservationChecker_atomic_Participant_Abort_atomic_SetParticipantAborted(first_xid: int, 
    first_mid: int, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657)
{

  init:
    call atomic_SetParticipantAborted(second_xid, second_mid, second_pair);
    assert true ==> Aborted(state[first_xid][CoordinatorMid]);
    assert true ==> xUndecidedOrAborted(state[first_xid]);
    assert true ==> participantMid(first_mid);
    return;
}



procedure Civl_GatePreservationChecker_atomic_Participant_Abort_atomic_SetParticipantAborted(first_xid: int, 
    first_mid: int, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657);
  requires true;
  requires Aborted(state[first_xid][CoordinatorMid]);
  requires xUndecidedOrAborted(state[first_xid]);
  requires participantMid(first_mid);
  requires xUndecidedOrAborted(state[second_xid]);
  requires pair(second_xid, second_mid, second_pair->val);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_FailurePreservationChecker_atomic_SetParticipantAborted_atomic_Participant_Abort(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int)
{

  init:
    call atomic_Participant_Abort(second_xid, second_mid);
    assert true
       ==> !(xUndecidedOrAborted(state[first_xid])
         && pair(first_xid, first_mid, first_pair->val));
    return;
}



procedure Civl_FailurePreservationChecker_atomic_SetParticipantAborted_atomic_Participant_Abort(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int);
  requires true;
  requires !(xUndecidedOrAborted(state[first_xid])
     && pair(first_xid, first_mid, first_pair->val));
  requires Aborted(state[second_xid][CoordinatorMid]);
  requires xUndecidedOrAborted(state[second_xid]);
  requires participantMid(second_mid);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_CommutativityChecker_atomic_StateUpdateOnVoteYes_atomic_Participant_Commit(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int)
   returns (first_commit: bool)
{

  init:
    call first_commit := atomic_StateUpdateOnVoteYes(first_xid, first_mid, first_pair);
    call atomic_Participant_Commit(second_xid, second_mid);
    assert (exists Civl_partition_Pair: [Pair]int :: 
          MapImp_4812(Set_Collector_5714(UnallocatedXids), 
                MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
               == MapConst_5_4577(true)
             && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
               == MapConst_5_4577(true))
         && (exists Civl_partition_Pair: [Pair]int :: 
          MapImp_4812(Set_Collector_5714(UnallocatedXids), 
                MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
               == MapConst_5_4577(true)
             && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
               == MapConst_5_4577(true))
       ==> (
          votes[first_xid] == -1
           && state
             == old(state)[second_xid := old(state)[second_xid][second_mid := COMMITTED()]]
           && B == Set_Add_4588(old(B), first_pair->val)
           && (first_commit <==> false)
           && votes == old(votes)
           && UnallocatedXids == old(UnallocatedXids))
         || (
          old(votes)[first_xid] != -1
           && B == Set_Add_4588(old(B), first_pair->val)
           && votes == old(votes)[first_xid := old(votes)[first_xid] + 1]
           && (first_commit <==> votes[first_xid] == numParticipants)
           && state
             == old(state)[second_xid := old(state)[second_xid][second_mid := COMMITTED()]][first_xid := old(state)[second_xid := old(state)[second_xid][second_mid := COMMITTED()]][first_xid][CoordinatorMid := (if first_commit
               then COMMITTED()
               else old(state)[second_xid := old(state)[second_xid][second_mid := COMMITTED()]][first_xid][CoordinatorMid])]]
           && UnallocatedXids == old(UnallocatedXids));
    return;
}



procedure Civl_CommutativityChecker_atomic_StateUpdateOnVoteYes_atomic_Participant_Commit(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int)
   returns (first_commit: bool);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(first_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
         == MapConst_5_4577(true));
  requires VotesEqCoordinatorState(votes, state, first_xid);
  requires Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids);
  requires Committed(state[second_xid][CoordinatorMid]);
  requires xUndecidedOrCommitted(state[second_xid]);
  requires participantMid(second_mid);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_GatePreservationChecker_atomic_Participant_Commit_atomic_StateUpdateOnVoteYes(first_xid: int, 
    first_mid: int, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657)
   returns (second_commit: bool)
{

  init:
    call second_commit := atomic_StateUpdateOnVoteYes(second_xid, second_mid, second_pair);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true))
       ==> Committed(state[first_xid][CoordinatorMid]);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true))
       ==> xUndecidedOrCommitted(state[first_xid]);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true))
       ==> participantMid(first_mid);
    return;
}



procedure Civl_GatePreservationChecker_atomic_Participant_Commit_atomic_StateUpdateOnVoteYes(first_xid: int, 
    first_mid: int, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657)
   returns (second_commit: bool);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(second_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
         == MapConst_5_4577(true));
  requires Committed(state[first_xid][CoordinatorMid]);
  requires xUndecidedOrCommitted(state[first_xid]);
  requires participantMid(first_mid);
  requires VotesEqCoordinatorState(votes, state, second_xid);
  requires Set_IsDisjoint_4577(perm(second_xid), UnallocatedXids);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_FailurePreservationChecker_atomic_StateUpdateOnVoteYes_atomic_Participant_Commit(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int)
   returns (first_commit: bool)
{

  init:
    call atomic_Participant_Commit(second_xid, second_mid);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true))
       ==> !(VotesEqCoordinatorState(votes, state, first_xid)
         && Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids));
    return;
}



procedure Civl_FailurePreservationChecker_atomic_StateUpdateOnVoteYes_atomic_Participant_Commit(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int)
   returns (first_commit: bool);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(first_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true));
  requires !(VotesEqCoordinatorState(votes, state, first_xid)
     && Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids));
  requires Committed(state[second_xid][CoordinatorMid]);
  requires xUndecidedOrCommitted(state[second_xid]);
  requires participantMid(second_mid);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_CommutativityChecker_atomic_StateUpdateOnVoteYes_atomic_Participant_Abort(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int)
   returns (first_commit: bool)
{

  init:
    call first_commit := atomic_StateUpdateOnVoteYes(first_xid, first_mid, first_pair);
    call atomic_Participant_Abort(second_xid, second_mid);
    assert (exists Civl_partition_Pair: [Pair]int :: 
          MapImp_4812(Set_Collector_5714(UnallocatedXids), 
                MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
               == MapConst_5_4577(true)
             && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
               == MapConst_5_4577(true))
         && (exists Civl_partition_Pair: [Pair]int :: 
          MapImp_4812(Set_Collector_5714(UnallocatedXids), 
                MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
               == MapConst_5_4577(true)
             && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
               == MapConst_5_4577(true))
       ==> (
          votes[first_xid] == -1
           && state
             == old(state)[second_xid := old(state)[second_xid][second_mid := ABORTED()]]
           && B == Set_Add_4588(old(B), first_pair->val)
           && (first_commit <==> false)
           && votes == old(votes)
           && UnallocatedXids == old(UnallocatedXids))
         || (
          old(votes)[first_xid] != -1
           && B == Set_Add_4588(old(B), first_pair->val)
           && votes == old(votes)[first_xid := old(votes)[first_xid] + 1]
           && (first_commit <==> votes[first_xid] == numParticipants)
           && state
             == old(state)[second_xid := old(state)[second_xid][second_mid := ABORTED()]][first_xid := old(state)[second_xid := old(state)[second_xid][second_mid := ABORTED()]][first_xid][CoordinatorMid := (if first_commit
               then COMMITTED()
               else old(state)[second_xid := old(state)[second_xid][second_mid := ABORTED()]][first_xid][CoordinatorMid])]]
           && UnallocatedXids == old(UnallocatedXids));
    return;
}



procedure Civl_CommutativityChecker_atomic_StateUpdateOnVoteYes_atomic_Participant_Abort(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int)
   returns (first_commit: bool);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(first_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
         == MapConst_5_4577(true));
  requires VotesEqCoordinatorState(votes, state, first_xid);
  requires Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids);
  requires Aborted(state[second_xid][CoordinatorMid]);
  requires xUndecidedOrAborted(state[second_xid]);
  requires participantMid(second_mid);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_GatePreservationChecker_atomic_Participant_Abort_atomic_StateUpdateOnVoteYes(first_xid: int, 
    first_mid: int, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657)
   returns (second_commit: bool)
{

  init:
    call second_commit := atomic_StateUpdateOnVoteYes(second_xid, second_mid, second_pair);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true))
       ==> Aborted(state[first_xid][CoordinatorMid]);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true))
       ==> xUndecidedOrAborted(state[first_xid]);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true))
       ==> participantMid(first_mid);
    return;
}



procedure Civl_GatePreservationChecker_atomic_Participant_Abort_atomic_StateUpdateOnVoteYes(first_xid: int, 
    first_mid: int, 
    second_xid: int, 
    second_mid: int, 
    second_pair: One_6657)
   returns (second_commit: bool);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(second_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
         == MapConst_5_4577(true));
  requires Aborted(state[first_xid][CoordinatorMid]);
  requires xUndecidedOrAborted(state[first_xid]);
  requires participantMid(first_mid);
  requires VotesEqCoordinatorState(votes, state, second_xid);
  requires Set_IsDisjoint_4577(perm(second_xid), UnallocatedXids);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_FailurePreservationChecker_atomic_StateUpdateOnVoteYes_atomic_Participant_Abort(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int)
   returns (first_commit: bool)
{

  init:
    call atomic_Participant_Abort(second_xid, second_mid);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true))
       ==> !(VotesEqCoordinatorState(votes, state, first_xid)
         && Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids));
    return;
}



procedure Civl_FailurePreservationChecker_atomic_StateUpdateOnVoteYes_atomic_Participant_Abort(first_xid: int, 
    first_mid: int, 
    first_pair: One_6657, 
    second_xid: int, 
    second_mid: int)
   returns (first_commit: bool);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(first_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true));
  requires !(VotesEqCoordinatorState(votes, state, first_xid)
     && Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids));
  requires Aborted(state[second_xid][CoordinatorMid]);
  requires xUndecidedOrAborted(state[second_xid]);
  requires participantMid(second_mid);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_CommutativityChecker_atomic_StateUpdateOnVoteNo_atomic_Participant_Commit(first_xid: int, first_mid: int, second_xid: int, second_mid: int)
   returns (first_abort: bool)
{

  init:
    call first_abort := atomic_StateUpdateOnVoteNo(first_xid, first_mid);
    call atomic_Participant_Commit(second_xid, second_mid);
    assert true
       ==> (first_abort <==> old(votes)[first_xid] != -1)
         && votes == old(votes)[first_xid := -1]
         && state
           == old(state)[second_xid := old(state)[second_xid][second_mid := COMMITTED()]][first_xid := old(state)[second_xid := old(state)[second_xid][second_mid := COMMITTED()]][first_xid][CoordinatorMid := (if first_abort
             then ABORTED()
             else old(state)[second_xid := old(state)[second_xid][second_mid := COMMITTED()]][first_xid][CoordinatorMid])]]
         && UnallocatedXids == old(UnallocatedXids);
    return;
}



procedure Civl_CommutativityChecker_atomic_StateUpdateOnVoteNo_atomic_Participant_Commit(first_xid: int, first_mid: int, second_xid: int, second_mid: int)
   returns (first_abort: bool);
  requires true;
  requires !Committed(state[first_xid][CoordinatorMid]);
  requires Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids);
  requires Committed(state[second_xid][CoordinatorMid]);
  requires xUndecidedOrCommitted(state[second_xid]);
  requires participantMid(second_mid);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_GatePreservationChecker_atomic_Participant_Commit_atomic_StateUpdateOnVoteNo(first_xid: int, first_mid: int, second_xid: int, second_mid: int)
   returns (second_abort: bool)
{

  init:
    call second_abort := atomic_StateUpdateOnVoteNo(second_xid, second_mid);
    assert true ==> Committed(state[first_xid][CoordinatorMid]);
    assert true ==> xUndecidedOrCommitted(state[first_xid]);
    assert true ==> participantMid(first_mid);
    return;
}



procedure Civl_GatePreservationChecker_atomic_Participant_Commit_atomic_StateUpdateOnVoteNo(first_xid: int, first_mid: int, second_xid: int, second_mid: int)
   returns (second_abort: bool);
  requires true;
  requires Committed(state[first_xid][CoordinatorMid]);
  requires xUndecidedOrCommitted(state[first_xid]);
  requires participantMid(first_mid);
  requires !Committed(state[second_xid][CoordinatorMid]);
  requires Set_IsDisjoint_4577(perm(second_xid), UnallocatedXids);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_FailurePreservationChecker_atomic_StateUpdateOnVoteNo_atomic_Participant_Commit(first_xid: int, first_mid: int, second_xid: int, second_mid: int)
   returns (first_abort: bool)
{

  init:
    call atomic_Participant_Commit(second_xid, second_mid);
    assert true
       ==> !(!Committed(state[first_xid][CoordinatorMid])
         && Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids));
    return;
}



procedure Civl_FailurePreservationChecker_atomic_StateUpdateOnVoteNo_atomic_Participant_Commit(first_xid: int, first_mid: int, second_xid: int, second_mid: int)
   returns (first_abort: bool);
  requires true;
  requires !(!Committed(state[first_xid][CoordinatorMid])
     && Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids));
  requires Committed(state[second_xid][CoordinatorMid]);
  requires xUndecidedOrCommitted(state[second_xid]);
  requires participantMid(second_mid);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_CommutativityChecker_atomic_StateUpdateOnVoteNo_atomic_Participant_Abort(first_xid: int, first_mid: int, second_xid: int, second_mid: int)
   returns (first_abort: bool)
{

  init:
    call first_abort := atomic_StateUpdateOnVoteNo(first_xid, first_mid);
    call atomic_Participant_Abort(second_xid, second_mid);
    assert true
       ==> (first_abort <==> old(votes)[first_xid] != -1)
         && votes == old(votes)[first_xid := -1]
         && state
           == old(state)[second_xid := old(state)[second_xid][second_mid := ABORTED()]][first_xid := old(state)[second_xid := old(state)[second_xid][second_mid := ABORTED()]][first_xid][CoordinatorMid := (if first_abort
             then ABORTED()
             else old(state)[second_xid := old(state)[second_xid][second_mid := ABORTED()]][first_xid][CoordinatorMid])]]
         && UnallocatedXids == old(UnallocatedXids);
    return;
}



procedure Civl_CommutativityChecker_atomic_StateUpdateOnVoteNo_atomic_Participant_Abort(first_xid: int, first_mid: int, second_xid: int, second_mid: int)
   returns (first_abort: bool);
  requires true;
  requires !Committed(state[first_xid][CoordinatorMid]);
  requires Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids);
  requires Aborted(state[second_xid][CoordinatorMid]);
  requires xUndecidedOrAborted(state[second_xid]);
  requires participantMid(second_mid);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_GatePreservationChecker_atomic_Participant_Abort_atomic_StateUpdateOnVoteNo(first_xid: int, first_mid: int, second_xid: int, second_mid: int)
   returns (second_abort: bool)
{

  init:
    call second_abort := atomic_StateUpdateOnVoteNo(second_xid, second_mid);
    assert true ==> Aborted(state[first_xid][CoordinatorMid]);
    assert true ==> xUndecidedOrAborted(state[first_xid]);
    assert true ==> participantMid(first_mid);
    return;
}



procedure Civl_GatePreservationChecker_atomic_Participant_Abort_atomic_StateUpdateOnVoteNo(first_xid: int, first_mid: int, second_xid: int, second_mid: int)
   returns (second_abort: bool);
  requires true;
  requires Aborted(state[first_xid][CoordinatorMid]);
  requires xUndecidedOrAborted(state[first_xid]);
  requires participantMid(first_mid);
  requires !Committed(state[second_xid][CoordinatorMid]);
  requires Set_IsDisjoint_4577(perm(second_xid), UnallocatedXids);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_FailurePreservationChecker_atomic_StateUpdateOnVoteNo_atomic_Participant_Abort(first_xid: int, first_mid: int, second_xid: int, second_mid: int)
   returns (first_abort: bool)
{

  init:
    call atomic_Participant_Abort(second_xid, second_mid);
    assert true
       ==> !(!Committed(state[first_xid][CoordinatorMid])
         && Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids));
    return;
}



procedure Civl_FailurePreservationChecker_atomic_StateUpdateOnVoteNo_atomic_Participant_Abort(first_xid: int, first_mid: int, second_xid: int, second_mid: int)
   returns (first_abort: bool);
  requires true;
  requires !(!Committed(state[first_xid][CoordinatorMid])
     && Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids));
  requires Aborted(state[second_xid][CoordinatorMid]);
  requires xUndecidedOrAborted(state[second_xid]);
  requires participantMid(second_mid);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_CommutativityChecker_atomic_Participant_Commit_atomic_Participant_Commit(first_xid: int, first_mid: int, second_xid: int, second_mid: int)
{

  init:
    call atomic_Participant_Commit(first_xid, first_mid);
    call atomic_Participant_Commit(second_xid, second_mid);
    assert true
       ==> state
         == old(state)[second_xid := old(state)[second_xid][second_mid := COMMITTED()]][first_xid := old(state)[second_xid := old(state)[second_xid][second_mid := COMMITTED()]][first_xid][first_mid := COMMITTED()]];
    return;
}



procedure Civl_CommutativityChecker_atomic_Participant_Commit_atomic_Participant_Commit(first_xid: int, first_mid: int, second_xid: int, second_mid: int);
  requires true;
  requires Committed(state[first_xid][CoordinatorMid]);
  requires xUndecidedOrCommitted(state[first_xid]);
  requires participantMid(first_mid);
  requires Committed(state[second_xid][CoordinatorMid]);
  requires xUndecidedOrCommitted(state[second_xid]);
  requires participantMid(second_mid);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_GatePreservationChecker_atomic_Participant_Commit_atomic_Participant_Commit(first_xid: int, first_mid: int, second_xid: int, second_mid: int)
{

  init:
    call atomic_Participant_Commit(second_xid, second_mid);
    assert true ==> Committed(state[first_xid][CoordinatorMid]);
    assert true ==> xUndecidedOrCommitted(state[first_xid]);
    assert true ==> participantMid(first_mid);
    return;
}



procedure Civl_GatePreservationChecker_atomic_Participant_Commit_atomic_Participant_Commit(first_xid: int, first_mid: int, second_xid: int, second_mid: int);
  requires true;
  requires Committed(state[first_xid][CoordinatorMid]);
  requires xUndecidedOrCommitted(state[first_xid]);
  requires participantMid(first_mid);
  requires Committed(state[second_xid][CoordinatorMid]);
  requires xUndecidedOrCommitted(state[second_xid]);
  requires participantMid(second_mid);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_FailurePreservationChecker_atomic_Participant_Commit_atomic_Participant_Commit(first_xid: int, first_mid: int, second_xid: int, second_mid: int)
{

  init:
    call atomic_Participant_Commit(second_xid, second_mid);
    assert true
       ==> !(
        Committed(state[first_xid][CoordinatorMid])
         && xUndecidedOrCommitted(state[first_xid])
         && participantMid(first_mid));
    return;
}



procedure Civl_FailurePreservationChecker_atomic_Participant_Commit_atomic_Participant_Commit(first_xid: int, first_mid: int, second_xid: int, second_mid: int);
  requires true;
  requires !(
    Committed(state[first_xid][CoordinatorMid])
     && xUndecidedOrCommitted(state[first_xid])
     && participantMid(first_mid));
  requires Committed(state[second_xid][CoordinatorMid]);
  requires xUndecidedOrCommitted(state[second_xid]);
  requires participantMid(second_mid);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_CommutativityChecker_atomic_Participant_Commit_atomic_Participant_Abort(first_xid: int, first_mid: int, second_xid: int, second_mid: int)
{

  init:
    call atomic_Participant_Commit(first_xid, first_mid);
    call atomic_Participant_Abort(second_xid, second_mid);
    assert true
       ==> state
         == old(state)[second_xid := old(state)[second_xid][second_mid := ABORTED()]][first_xid := old(state)[second_xid := old(state)[second_xid][second_mid := ABORTED()]][first_xid][first_mid := COMMITTED()]];
    return;
}



procedure Civl_CommutativityChecker_atomic_Participant_Commit_atomic_Participant_Abort(first_xid: int, first_mid: int, second_xid: int, second_mid: int);
  requires true;
  requires Committed(state[first_xid][CoordinatorMid]);
  requires xUndecidedOrCommitted(state[first_xid]);
  requires participantMid(first_mid);
  requires Aborted(state[second_xid][CoordinatorMid]);
  requires xUndecidedOrAborted(state[second_xid]);
  requires participantMid(second_mid);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_GatePreservationChecker_atomic_Participant_Abort_atomic_Participant_Commit(first_xid: int, first_mid: int, second_xid: int, second_mid: int)
{

  init:
    call atomic_Participant_Commit(second_xid, second_mid);
    assert true ==> Aborted(state[first_xid][CoordinatorMid]);
    assert true ==> xUndecidedOrAborted(state[first_xid]);
    assert true ==> participantMid(first_mid);
    return;
}



procedure Civl_GatePreservationChecker_atomic_Participant_Abort_atomic_Participant_Commit(first_xid: int, first_mid: int, second_xid: int, second_mid: int);
  requires true;
  requires Aborted(state[first_xid][CoordinatorMid]);
  requires xUndecidedOrAborted(state[first_xid]);
  requires participantMid(first_mid);
  requires Committed(state[second_xid][CoordinatorMid]);
  requires xUndecidedOrCommitted(state[second_xid]);
  requires participantMid(second_mid);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_FailurePreservationChecker_atomic_Participant_Commit_atomic_Participant_Abort(first_xid: int, first_mid: int, second_xid: int, second_mid: int)
{

  init:
    call atomic_Participant_Abort(second_xid, second_mid);
    assert true
       ==> !(
        Committed(state[first_xid][CoordinatorMid])
         && xUndecidedOrCommitted(state[first_xid])
         && participantMid(first_mid));
    return;
}



procedure Civl_FailurePreservationChecker_atomic_Participant_Commit_atomic_Participant_Abort(first_xid: int, first_mid: int, second_xid: int, second_mid: int);
  requires true;
  requires !(
    Committed(state[first_xid][CoordinatorMid])
     && xUndecidedOrCommitted(state[first_xid])
     && participantMid(first_mid));
  requires Aborted(state[second_xid][CoordinatorMid]);
  requires xUndecidedOrAborted(state[second_xid]);
  requires participantMid(second_mid);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_CommutativityChecker_atomic_Participant_Abort_atomic_Participant_Commit(first_xid: int, first_mid: int, second_xid: int, second_mid: int)
{

  init:
    call atomic_Participant_Abort(first_xid, first_mid);
    call atomic_Participant_Commit(second_xid, second_mid);
    assert true
       ==> state
         == old(state)[second_xid := old(state)[second_xid][second_mid := COMMITTED()]][first_xid := old(state)[second_xid := old(state)[second_xid][second_mid := COMMITTED()]][first_xid][first_mid := ABORTED()]];
    return;
}



procedure Civl_CommutativityChecker_atomic_Participant_Abort_atomic_Participant_Commit(first_xid: int, first_mid: int, second_xid: int, second_mid: int);
  requires true;
  requires Aborted(state[first_xid][CoordinatorMid]);
  requires xUndecidedOrAborted(state[first_xid]);
  requires participantMid(first_mid);
  requires Committed(state[second_xid][CoordinatorMid]);
  requires xUndecidedOrCommitted(state[second_xid]);
  requires participantMid(second_mid);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_GatePreservationChecker_atomic_Participant_Commit_atomic_Participant_Abort(first_xid: int, first_mid: int, second_xid: int, second_mid: int)
{

  init:
    call atomic_Participant_Abort(second_xid, second_mid);
    assert true ==> Committed(state[first_xid][CoordinatorMid]);
    assert true ==> xUndecidedOrCommitted(state[first_xid]);
    assert true ==> participantMid(first_mid);
    return;
}



procedure Civl_GatePreservationChecker_atomic_Participant_Commit_atomic_Participant_Abort(first_xid: int, first_mid: int, second_xid: int, second_mid: int);
  requires true;
  requires Committed(state[first_xid][CoordinatorMid]);
  requires xUndecidedOrCommitted(state[first_xid]);
  requires participantMid(first_mid);
  requires Aborted(state[second_xid][CoordinatorMid]);
  requires xUndecidedOrAborted(state[second_xid]);
  requires participantMid(second_mid);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_FailurePreservationChecker_atomic_Participant_Abort_atomic_Participant_Commit(first_xid: int, first_mid: int, second_xid: int, second_mid: int)
{

  init:
    call atomic_Participant_Commit(second_xid, second_mid);
    assert true
       ==> !(
        Aborted(state[first_xid][CoordinatorMid])
         && xUndecidedOrAborted(state[first_xid])
         && participantMid(first_mid));
    return;
}



procedure Civl_FailurePreservationChecker_atomic_Participant_Abort_atomic_Participant_Commit(first_xid: int, first_mid: int, second_xid: int, second_mid: int);
  requires true;
  requires !(
    Aborted(state[first_xid][CoordinatorMid])
     && xUndecidedOrAborted(state[first_xid])
     && participantMid(first_mid));
  requires Committed(state[second_xid][CoordinatorMid]);
  requires xUndecidedOrCommitted(state[second_xid]);
  requires participantMid(second_mid);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_CommutativityChecker_atomic_Participant_Abort_atomic_Participant_Abort(first_xid: int, first_mid: int, second_xid: int, second_mid: int)
{

  init:
    call atomic_Participant_Abort(first_xid, first_mid);
    call atomic_Participant_Abort(second_xid, second_mid);
    assert true
       ==> state
         == old(state)[second_xid := old(state)[second_xid][second_mid := ABORTED()]][first_xid := old(state)[second_xid := old(state)[second_xid][second_mid := ABORTED()]][first_xid][first_mid := ABORTED()]];
    return;
}



procedure Civl_CommutativityChecker_atomic_Participant_Abort_atomic_Participant_Abort(first_xid: int, first_mid: int, second_xid: int, second_mid: int);
  requires true;
  requires Aborted(state[first_xid][CoordinatorMid]);
  requires xUndecidedOrAborted(state[first_xid]);
  requires participantMid(first_mid);
  requires Aborted(state[second_xid][CoordinatorMid]);
  requires xUndecidedOrAborted(state[second_xid]);
  requires participantMid(second_mid);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_GatePreservationChecker_atomic_Participant_Abort_atomic_Participant_Abort(first_xid: int, first_mid: int, second_xid: int, second_mid: int)
{

  init:
    call atomic_Participant_Abort(second_xid, second_mid);
    assert true ==> Aborted(state[first_xid][CoordinatorMid]);
    assert true ==> xUndecidedOrAborted(state[first_xid]);
    assert true ==> participantMid(first_mid);
    return;
}



procedure Civl_GatePreservationChecker_atomic_Participant_Abort_atomic_Participant_Abort(first_xid: int, first_mid: int, second_xid: int, second_mid: int);
  requires true;
  requires Aborted(state[first_xid][CoordinatorMid]);
  requires xUndecidedOrAborted(state[first_xid]);
  requires participantMid(first_mid);
  requires Aborted(state[second_xid][CoordinatorMid]);
  requires xUndecidedOrAborted(state[second_xid]);
  requires participantMid(second_mid);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_FailurePreservationChecker_atomic_Participant_Abort_atomic_Participant_Abort(first_xid: int, first_mid: int, second_xid: int, second_mid: int)
{

  init:
    call atomic_Participant_Abort(second_xid, second_mid);
    assert true
       ==> !(
        Aborted(state[first_xid][CoordinatorMid])
         && xUndecidedOrAborted(state[first_xid])
         && participantMid(first_mid));
    return;
}



procedure Civl_FailurePreservationChecker_atomic_Participant_Abort_atomic_Participant_Abort(first_xid: int, first_mid: int, second_xid: int, second_mid: int);
  requires true;
  requires !(
    Aborted(state[first_xid][CoordinatorMid])
     && xUndecidedOrAborted(state[first_xid])
     && participantMid(first_mid));
  requires Aborted(state[second_xid][CoordinatorMid]);
  requires xUndecidedOrAborted(state[second_xid]);
  requires participantMid(second_mid);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_CommutativityChecker_atomic_AllocateXid_atomic_Participant_VoteReq(second_xid: int, second_mid: int, second_pair: One_6657)
   returns (first_xid: int, first_pairs: Set_5714)
{

  init:
    call first_xid, first_pairs := atomic_AllocateXid();
    call atomic_Participant_VoteReq(second_xid, second_mid, second_pair);
    assert (exists Civl_partition_Pair: [Pair]int :: 
          MapImp_4812(Set_Collector_5714(first_pairs), 
                MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
               == MapConst_5_4577(true)
             && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
                MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
               == MapConst_5_4577(true))
         && (exists Civl_partition_Pair: [Pair]int :: 
          MapImp_4812(Set_Collector_5714(first_pairs), 
                MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
               == MapConst_5_4577(true)
             && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
                MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
               == MapConst_5_4577(true))
       ==> (exists {:pool "A"} Civl_second_x#0: [int]int :: 
        { Trigger_atomic_Participant_VoteReq_x(Civl_second_x#0) } 
        xConsistentExtension(old(state)[second_xid], state[second_xid])
           && state[first_xid] == (lambda first_j: int :: UNDECIDED())
           && Set_IsSubset_4812(first_pairs, old(UnallocatedXids))
           && state == old(state)[second_xid := Civl_second_x#0]
           && first_pairs == perm(first_xid)
           && UnallocatedXids == Set_Difference_4590(old(UnallocatedXids), first_pairs));
    return;
}



procedure Civl_CommutativityChecker_atomic_AllocateXid_atomic_Participant_VoteReq(second_xid: int, second_mid: int, second_pair: One_6657)
   returns (first_xid: int, first_pairs: Set_5714);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(second_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true));
  requires (forall first_xid: int :: 
    state[first_xid] == (lambda first_j: int :: UNDECIDED())
       ==> 
      Set_IsSubset_4812(perm(first_xid), UnallocatedXids)
       ==> Set_IsSubset_4812(perm(first_xid), UnallocatedXids));
  requires xConsistent(state[second_xid]);
  requires pair(second_xid, second_mid, second_pair->val);
  requires Set_IsDisjoint_4577(perm(second_xid), UnallocatedXids);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_GatePreservationChecker_atomic_Participant_VoteReq_atomic_AllocateXid(first_xid: int, first_mid: int, first_pair: One_6657)
   returns (second_xid: int, second_pairs: Set_5714)
{

  init:
    call second_xid, second_pairs := atomic_AllocateXid();
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(second_pairs), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
             == MapConst_5_4577(true))
       ==> xConsistent(state[first_xid]);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(second_pairs), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
             == MapConst_5_4577(true))
       ==> pair(first_xid, first_mid, first_pair->val);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(second_pairs), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
             == MapConst_5_4577(true))
       ==> Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids);
    return;
}



procedure Civl_GatePreservationChecker_atomic_Participant_VoteReq_atomic_AllocateXid(first_xid: int, first_mid: int, first_pair: One_6657)
   returns (second_xid: int, second_pairs: Set_5714);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(first_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true));
  requires xConsistent(state[first_xid]);
  requires pair(first_xid, first_mid, first_pair->val);
  requires Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids);
  requires (forall second_xid: int :: 
    state[second_xid] == (lambda second_j: int :: UNDECIDED())
       ==> 
      Set_IsSubset_4812(perm(second_xid), UnallocatedXids)
       ==> Set_IsSubset_4812(perm(second_xid), UnallocatedXids));
  modifies state, votes, B, UnallocatedXids;



implementation Civl_FailurePreservationChecker_atomic_AllocateXid_atomic_Participant_VoteReq(second_xid: int, second_mid: int, second_pair: One_6657)
   returns (first_xid: int, first_pairs: Set_5714)
{

  init:
    call atomic_Participant_VoteReq(second_xid, second_mid, second_pair);
    assert true
       ==> !(forall first_xid: int :: 
        state[first_xid] == (lambda first_j: int :: UNDECIDED())
           ==> 
          Set_IsSubset_4812(perm(first_xid), UnallocatedXids)
           ==> Set_IsSubset_4812(perm(first_xid), UnallocatedXids));
    return;
}



procedure Civl_FailurePreservationChecker_atomic_AllocateXid_atomic_Participant_VoteReq(second_xid: int, second_mid: int, second_pair: One_6657)
   returns (first_xid: int, first_pairs: Set_5714);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(second_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true));
  requires !(forall first_xid: int :: 
    state[first_xid] == (lambda first_j: int :: UNDECIDED())
       ==> 
      Set_IsSubset_4812(perm(first_xid), UnallocatedXids)
       ==> Set_IsSubset_4812(perm(first_xid), UnallocatedXids));
  requires xConsistent(state[second_xid]);
  requires pair(second_xid, second_mid, second_pair->val);
  requires Set_IsDisjoint_4577(perm(second_xid), UnallocatedXids);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_CommutativityChecker_atomic_AllocateXid_atomic_Coordinator_VoteYes(second_xid: int, second_mid: int, second_pair: One_6657)
   returns (first_xid: int, first_pairs: Set_5714)
{

  init:
    call first_xid, first_pairs := atomic_AllocateXid();
    call atomic_Coordinator_VoteYes(second_xid, second_mid, second_pair);
    assert (exists Civl_partition_Pair: [Pair]int :: 
          MapImp_4812(Set_Collector_5714(first_pairs), 
                MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
               == MapConst_5_4577(true)
             && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
                MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
               == MapConst_5_4577(true)
             && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
               == MapConst_5_4577(true))
         && (exists Civl_partition_Pair: [Pair]int :: 
          MapImp_4812(Set_Collector_5714(first_pairs), 
                MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
               == MapConst_5_4577(true)
             && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
                MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
               == MapConst_5_4577(true)
             && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
               == MapConst_5_4577(true))
       ==> (exists {:pool "A"} Civl_second_x#0: [int]int :: 
          { Trigger_atomic_Coordinator_VoteYes_x(Civl_second_x#0) } 
          xAllParticipantsInB(second_xid, B)
             && xConsistentExtension(old(state)[second_xid], state[second_xid])
             && state[first_xid] == (lambda first_j: int :: UNDECIDED())
             && Set_IsSubset_4812(first_pairs, old(UnallocatedXids))
             && B == Set_Add_4588(old(B), second_pair->val)
             && state == old(state)[second_xid := Civl_second_x#0]
             && first_pairs == perm(first_xid)
             && UnallocatedXids == Set_Difference_4590(old(UnallocatedXids), first_pairs))
         || (
          state[first_xid] == (lambda first_j: int :: UNDECIDED())
           && Set_IsSubset_4812(first_pairs, old(UnallocatedXids))
           && B == Set_Add_4588(old(B), second_pair->val)
           && first_pairs == perm(first_xid)
           && UnallocatedXids == Set_Difference_4590(old(UnallocatedXids), first_pairs)
           && state == old(state));
    return;
}



procedure Civl_CommutativityChecker_atomic_AllocateXid_atomic_Coordinator_VoteYes(second_xid: int, second_mid: int, second_pair: One_6657)
   returns (first_xid: int, first_pairs: Set_5714);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(second_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
         == MapConst_5_4577(true));
  requires (forall first_xid: int :: 
    state[first_xid] == (lambda first_j: int :: UNDECIDED())
       ==> 
      Set_IsSubset_4812(perm(first_xid), UnallocatedXids)
       ==> Set_IsSubset_4812(perm(first_xid), UnallocatedXids));
  requires xConsistent(state[second_xid]);
  requires pair(second_xid, second_mid, second_pair->val);
  requires Set_IsDisjoint_4577(perm(second_xid), UnallocatedXids);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_GatePreservationChecker_atomic_Coordinator_VoteYes_atomic_AllocateXid(first_xid: int, first_mid: int, first_pair: One_6657)
   returns (second_xid: int, second_pairs: Set_5714)
{

  init:
    call second_xid, second_pairs := atomic_AllocateXid();
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(second_pairs), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
             == MapConst_5_4577(true))
       ==> xConsistent(state[first_xid]);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(second_pairs), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
             == MapConst_5_4577(true))
       ==> pair(first_xid, first_mid, first_pair->val);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(second_pairs), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
             == MapConst_5_4577(true))
       ==> Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids);
    return;
}



procedure Civl_GatePreservationChecker_atomic_Coordinator_VoteYes_atomic_AllocateXid(first_xid: int, first_mid: int, first_pair: One_6657)
   returns (second_xid: int, second_pairs: Set_5714);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(first_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true));
  requires xConsistent(state[first_xid]);
  requires pair(first_xid, first_mid, first_pair->val);
  requires Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids);
  requires (forall second_xid: int :: 
    state[second_xid] == (lambda second_j: int :: UNDECIDED())
       ==> 
      Set_IsSubset_4812(perm(second_xid), UnallocatedXids)
       ==> Set_IsSubset_4812(perm(second_xid), UnallocatedXids));
  modifies state, votes, B, UnallocatedXids;



implementation Civl_FailurePreservationChecker_atomic_AllocateXid_atomic_Coordinator_VoteYes(second_xid: int, second_mid: int, second_pair: One_6657)
   returns (first_xid: int, first_pairs: Set_5714)
{

  init:
    call atomic_Coordinator_VoteYes(second_xid, second_mid, second_pair);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true))
       ==> !(forall first_xid: int :: 
        state[first_xid] == (lambda first_j: int :: UNDECIDED())
           ==> 
          Set_IsSubset_4812(perm(first_xid), UnallocatedXids)
           ==> Set_IsSubset_4812(perm(first_xid), UnallocatedXids));
    return;
}



procedure Civl_FailurePreservationChecker_atomic_AllocateXid_atomic_Coordinator_VoteYes(second_xid: int, second_mid: int, second_pair: One_6657)
   returns (first_xid: int, first_pairs: Set_5714);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(second_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
         == MapConst_5_4577(true));
  requires !(forall first_xid: int :: 
    state[first_xid] == (lambda first_j: int :: UNDECIDED())
       ==> 
      Set_IsSubset_4812(perm(first_xid), UnallocatedXids)
       ==> Set_IsSubset_4812(perm(first_xid), UnallocatedXids));
  requires xConsistent(state[second_xid]);
  requires pair(second_xid, second_mid, second_pair->val);
  requires Set_IsDisjoint_4577(perm(second_xid), UnallocatedXids);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_CommutativityChecker_atomic_AllocateXid_atomic_Coordinator_VoteNo(second_xid: int, second_mid: int, second_pair: One_6657)
   returns (first_xid: int, first_pairs: Set_5714)
{

  init:
    call first_xid, first_pairs := atomic_AllocateXid();
    call atomic_Coordinator_VoteNo(second_xid, second_mid, second_pair);
    assert (exists Civl_partition_Pair: [Pair]int :: 
          MapImp_4812(Set_Collector_5714(first_pairs), 
                MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
               == MapConst_5_4577(true)
             && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
                MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
               == MapConst_5_4577(true))
         && (exists Civl_partition_Pair: [Pair]int :: 
          MapImp_4812(Set_Collector_5714(first_pairs), 
                MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
               == MapConst_5_4577(true)
             && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
                MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
               == MapConst_5_4577(true))
       ==> (exists {:pool "A"} Civl_second_x#0: [int]int :: 
        { Trigger_atomic_Coordinator_VoteNo_x(Civl_second_x#0) } 
        xUndecidedOrAborted(state[second_xid])
           && xConsistentExtension(old(state)[second_xid], state[second_xid])
           && state[first_xid] == (lambda first_j: int :: UNDECIDED())
           && Set_IsSubset_4812(first_pairs, old(UnallocatedXids))
           && state == old(state)[second_xid := Civl_second_x#0]
           && first_pairs == perm(first_xid)
           && UnallocatedXids == Set_Difference_4590(old(UnallocatedXids), first_pairs));
    return;
}



procedure Civl_CommutativityChecker_atomic_AllocateXid_atomic_Coordinator_VoteNo(second_xid: int, second_mid: int, second_pair: One_6657)
   returns (first_xid: int, first_pairs: Set_5714);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(second_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true));
  requires (forall first_xid: int :: 
    state[first_xid] == (lambda first_j: int :: UNDECIDED())
       ==> 
      Set_IsSubset_4812(perm(first_xid), UnallocatedXids)
       ==> Set_IsSubset_4812(perm(first_xid), UnallocatedXids));
  requires xUndecidedOrAborted(state[second_xid]);
  requires pair(second_xid, second_mid, second_pair->val);
  requires Set_IsDisjoint_4577(perm(second_xid), UnallocatedXids);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_GatePreservationChecker_atomic_Coordinator_VoteNo_atomic_AllocateXid(first_xid: int, first_mid: int, first_pair: One_6657)
   returns (second_xid: int, second_pairs: Set_5714)
{

  init:
    call second_xid, second_pairs := atomic_AllocateXid();
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(second_pairs), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
             == MapConst_5_4577(true))
       ==> xUndecidedOrAborted(state[first_xid]);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(second_pairs), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
             == MapConst_5_4577(true))
       ==> pair(first_xid, first_mid, first_pair->val);
    assert (exists Civl_partition_Pair: [Pair]int :: 
        MapImp_4812(One_Collector_6657(first_pair), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(second_pairs), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
             == MapConst_5_4577(true)
           && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
              MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
             == MapConst_5_4577(true))
       ==> Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids);
    return;
}



procedure Civl_GatePreservationChecker_atomic_Coordinator_VoteNo_atomic_AllocateXid(first_xid: int, first_mid: int, first_pair: One_6657)
   returns (second_xid: int, second_pairs: Set_5714);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(first_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true));
  requires xUndecidedOrAborted(state[first_xid]);
  requires pair(first_xid, first_mid, first_pair->val);
  requires Set_IsDisjoint_4577(perm(first_xid), UnallocatedXids);
  requires (forall second_xid: int :: 
    state[second_xid] == (lambda second_j: int :: UNDECIDED())
       ==> 
      Set_IsSubset_4812(perm(second_xid), UnallocatedXids)
       ==> Set_IsSubset_4812(perm(second_xid), UnallocatedXids));
  modifies state, votes, B, UnallocatedXids;



implementation Civl_FailurePreservationChecker_atomic_AllocateXid_atomic_Coordinator_VoteNo(second_xid: int, second_mid: int, second_pair: One_6657)
   returns (first_xid: int, first_pairs: Set_5714)
{

  init:
    call atomic_Coordinator_VoteNo(second_xid, second_mid, second_pair);
    assert true
       ==> !(forall first_xid: int :: 
        state[first_xid] == (lambda first_j: int :: UNDECIDED())
           ==> 
          Set_IsSubset_4812(perm(first_xid), UnallocatedXids)
           ==> Set_IsSubset_4812(perm(first_xid), UnallocatedXids));
    return;
}



procedure Civl_FailurePreservationChecker_atomic_AllocateXid_atomic_Coordinator_VoteNo(second_xid: int, second_mid: int, second_pair: One_6657)
   returns (first_xid: int, first_pairs: Set_5714);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(second_pair), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true));
  requires !(forall first_xid: int :: 
    state[first_xid] == (lambda first_j: int :: UNDECIDED())
       ==> 
      Set_IsSubset_4812(perm(first_xid), UnallocatedXids)
       ==> Set_IsSubset_4812(perm(first_xid), UnallocatedXids));
  requires xUndecidedOrAborted(state[second_xid]);
  requires pair(second_xid, second_mid, second_pair->val);
  requires Set_IsDisjoint_4577(perm(second_xid), UnallocatedXids);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_CommutativityChecker_atomic_AllocateXid_atomic_Participant_Commit(second_xid: int, second_mid: int)
   returns (first_xid: int, first_pairs: Set_5714)
{

  init:
    call first_xid, first_pairs := atomic_AllocateXid();
    call atomic_Participant_Commit(second_xid, second_mid);
    assert (exists Civl_partition_Pair: [Pair]int :: 
          MapImp_4812(Set_Collector_5714(first_pairs), 
                MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
               == MapConst_5_4577(true)
             && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
                MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
               == MapConst_5_4577(true))
         && (exists Civl_partition_Pair: [Pair]int :: 
          MapImp_4812(Set_Collector_5714(first_pairs), 
                MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
               == MapConst_5_4577(true)
             && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
                MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
               == MapConst_5_4577(true))
       ==> state[first_xid] == (lambda first_j: int :: UNDECIDED())
         && Set_IsSubset_4812(first_pairs, old(UnallocatedXids))
         && state
           == old(state)[second_xid := old(state)[second_xid][second_mid := COMMITTED()]]
         && first_pairs == perm(first_xid)
         && UnallocatedXids == Set_Difference_4590(old(UnallocatedXids), first_pairs);
    return;
}



procedure Civl_CommutativityChecker_atomic_AllocateXid_atomic_Participant_Commit(second_xid: int, second_mid: int)
   returns (first_xid: int, first_pairs: Set_5714);
  requires true;
  requires (forall first_xid: int :: 
    state[first_xid] == (lambda first_j: int :: UNDECIDED())
       ==> 
      Set_IsSubset_4812(perm(first_xid), UnallocatedXids)
       ==> Set_IsSubset_4812(perm(first_xid), UnallocatedXids));
  requires Committed(state[second_xid][CoordinatorMid]);
  requires xUndecidedOrCommitted(state[second_xid]);
  requires participantMid(second_mid);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_FailurePreservationChecker_atomic_AllocateXid_atomic_Participant_Commit(second_xid: int, second_mid: int)
   returns (first_xid: int, first_pairs: Set_5714)
{

  init:
    call atomic_Participant_Commit(second_xid, second_mid);
    assert true
       ==> !(forall first_xid: int :: 
        state[first_xid] == (lambda first_j: int :: UNDECIDED())
           ==> 
          Set_IsSubset_4812(perm(first_xid), UnallocatedXids)
           ==> Set_IsSubset_4812(perm(first_xid), UnallocatedXids));
    return;
}



procedure Civl_FailurePreservationChecker_atomic_AllocateXid_atomic_Participant_Commit(second_xid: int, second_mid: int)
   returns (first_xid: int, first_pairs: Set_5714);
  requires true;
  requires !(forall first_xid: int :: 
    state[first_xid] == (lambda first_j: int :: UNDECIDED())
       ==> 
      Set_IsSubset_4812(perm(first_xid), UnallocatedXids)
       ==> Set_IsSubset_4812(perm(first_xid), UnallocatedXids));
  requires Committed(state[second_xid][CoordinatorMid]);
  requires xUndecidedOrCommitted(state[second_xid]);
  requires participantMid(second_mid);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_CommutativityChecker_atomic_AllocateXid_atomic_Participant_Abort(second_xid: int, second_mid: int)
   returns (first_xid: int, first_pairs: Set_5714)
{

  init:
    call first_xid, first_pairs := atomic_AllocateXid();
    call atomic_Participant_Abort(second_xid, second_mid);
    assert (exists Civl_partition_Pair: [Pair]int :: 
          MapImp_4812(Set_Collector_5714(first_pairs), 
                MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
               == MapConst_5_4577(true)
             && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
                MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
               == MapConst_5_4577(true))
         && (exists Civl_partition_Pair: [Pair]int :: 
          MapImp_4812(Set_Collector_5714(first_pairs), 
                MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
               == MapConst_5_4577(true)
             && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
                MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
               == MapConst_5_4577(true))
       ==> state[first_xid] == (lambda first_j: int :: UNDECIDED())
         && Set_IsSubset_4812(first_pairs, old(UnallocatedXids))
         && state
           == old(state)[second_xid := old(state)[second_xid][second_mid := ABORTED()]]
         && first_pairs == perm(first_xid)
         && UnallocatedXids == Set_Difference_4590(old(UnallocatedXids), first_pairs);
    return;
}



procedure Civl_CommutativityChecker_atomic_AllocateXid_atomic_Participant_Abort(second_xid: int, second_mid: int)
   returns (first_xid: int, first_pairs: Set_5714);
  requires true;
  requires (forall first_xid: int :: 
    state[first_xid] == (lambda first_j: int :: UNDECIDED())
       ==> 
      Set_IsSubset_4812(perm(first_xid), UnallocatedXids)
       ==> Set_IsSubset_4812(perm(first_xid), UnallocatedXids));
  requires Aborted(state[second_xid][CoordinatorMid]);
  requires xUndecidedOrAborted(state[second_xid]);
  requires participantMid(second_mid);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_FailurePreservationChecker_atomic_AllocateXid_atomic_Participant_Abort(second_xid: int, second_mid: int)
   returns (first_xid: int, first_pairs: Set_5714)
{

  init:
    call atomic_Participant_Abort(second_xid, second_mid);
    assert true
       ==> !(forall first_xid: int :: 
        state[first_xid] == (lambda first_j: int :: UNDECIDED())
           ==> 
          Set_IsSubset_4812(perm(first_xid), UnallocatedXids)
           ==> Set_IsSubset_4812(perm(first_xid), UnallocatedXids));
    return;
}



procedure Civl_FailurePreservationChecker_atomic_AllocateXid_atomic_Participant_Abort(second_xid: int, second_mid: int)
   returns (first_xid: int, first_pairs: Set_5714);
  requires true;
  requires !(forall first_xid: int :: 
    state[first_xid] == (lambda first_j: int :: UNDECIDED())
       ==> 
      Set_IsSubset_4812(perm(first_xid), UnallocatedXids)
       ==> Set_IsSubset_4812(perm(first_xid), UnallocatedXids));
  requires Aborted(state[second_xid][CoordinatorMid]);
  requires xUndecidedOrAborted(state[second_xid]);
  requires participantMid(second_mid);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_CooperationChecker_atomic_Participant_VoteReq(xid: int, mid: int, pair: One_6657)
{

  init:
    assert (exists {:pool "A"} Civl_x#0: [int]int :: 
      xConsistentExtension(old(state)[xid], old(state)[xid := Civl_x#0][xid]));
    call atomic_Participant_VoteReq(xid, mid, pair);
    return;
}



procedure Civl_CooperationChecker_atomic_Participant_VoteReq(xid: int, mid: int, pair: One_6657);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(pair), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true));
  requires xConsistent(state[xid]);
  requires pair(xid, mid, pair->val);
  requires Set_IsDisjoint_4577(perm(xid), UnallocatedXids);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_CooperationChecker_atomic_Coordinator_VoteYes(xid: int, mid: int, pair: One_6657)
{

  init:
    assert true;
    call atomic_Coordinator_VoteYes(xid, mid, pair);
    return;
}



procedure Civl_CooperationChecker_atomic_Coordinator_VoteYes(xid: int, mid: int, pair: One_6657);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(pair), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
         == MapConst_5_4577(true));
  requires xConsistent(state[xid]);
  requires pair(xid, mid, pair->val);
  requires Set_IsDisjoint_4577(perm(xid), UnallocatedXids);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_CooperationChecker_atomic_Coordinator_VoteNo(xid: int, mid: int, pair: One_6657)
{

  init:
    assert (exists {:pool "A"} Civl_x#0: [int]int :: 
      xUndecidedOrAborted(old(state)[xid := Civl_x#0][xid])
         && xConsistentExtension(old(state)[xid], old(state)[xid := Civl_x#0][xid]));
    call atomic_Coordinator_VoteNo(xid, mid, pair);
    return;
}



procedure Civl_CooperationChecker_atomic_Coordinator_VoteNo(xid: int, mid: int, pair: One_6657);
  requires (exists Civl_partition_Pair: [Pair]int :: 
    MapImp_4812(One_Collector_6657(pair), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
         == MapConst_5_4577(true)
       && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
          MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
         == MapConst_5_4577(true));
  requires xUndecidedOrAborted(state[xid]);
  requires pair(xid, mid, pair->val);
  requires Set_IsDisjoint_4577(perm(xid), UnallocatedXids);
  modifies state, votes, B, UnallocatedXids;



procedure Civl_main_8();
  requires Inv_8(state, B, votes);
  modifies state, votes, B, UnallocatedXids;



procedure Civl_Coordinator_TransactionReq_8() returns (xid: int);
  requires Inv_8(state, B, votes);
  modifies state, votes, B, UnallocatedXids;
  ensures Inv_8(state, B, votes);



procedure Civl_Participant_VoteReq_8(xid: int, mid: int, pair: One_6657);
  requires Inv_8(state, B, votes);
  requires pair(xid, mid, pair->val)
     && (votes[xid] == -1 || UndecidedOrCommitted(state[xid][mid]));
  modifies state, votes, B, UnallocatedXids;



procedure Civl_Coordinator_VoteYes_8(xid: int, mid: int, pair: One_6657);
  requires Inv_8(state, B, votes);
  requires pair(xid, mid, pair->val)
     && (votes[xid] == -1 || UndecidedOrCommitted(state[xid][mid]));
  modifies state, votes, B, UnallocatedXids;



procedure Civl_Coordinator_VoteNo_8(xid: int, mid: int, pair: One_6657);
  requires pair(xid, mid, pair->val) && Aborted(state[xid][mid]);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_main_8()
{
  var xid: int;
  var Civl_global_old_state: [int][int]int;
  var Civl_global_old_votes: [int]int;
  var Civl_global_old_B: Set_5714;
  var Civl_global_old_UnallocatedXids: Set_5714;
  var Civl_linear_Pair_available: [Pair]bool;

  /*** structured program:
    while (*)
      invariant      call YieldInv_8();
      invariant      call YieldConsistent_9();
      invariant      call YieldConsistent_10();
      invariant {:yields} true;
    {
        call xid := Coordinator_TransactionReq();
    }
  **** end structured program */

  Civl_init:
    havoc state, votes, B, UnallocatedXids;
    assume (exists Civl_partition_Pair: [Pair]int :: 
      MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
           == MapConst_5_4577(true)
         && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
            MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
           == MapConst_5_4577(true));
    assume Inv_8(state, B, votes);
    Civl_global_old_state, Civl_global_old_votes, Civl_global_old_B, Civl_global_old_UnallocatedXids := state, votes, B, UnallocatedXids;
    Civl_linear_Pair_available := MapOr_5714(Set_Collector_5714(UnallocatedXids), 
      MapOr_5714(Set_Collector_5714(B), MapConst_5_4577(false)));
    goto anon0;

  anon0:
    goto anon2_LoopHead, Civl_NoninterferenceChecker, Civl_RefinementChecker;

  anon2_LoopHead:
    assume (exists Civl_partition_Pair: [Pair]int :: 
      MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
           == MapConst_5_4577(true)
         && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
            MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
           == MapConst_5_4577(true));
    assert Inv_8(state, B, votes);
    state, votes, B, UnallocatedXids := state, votes, B, UnallocatedXids;
    Civl_global_old_state, Civl_global_old_votes, Civl_global_old_B, Civl_global_old_UnallocatedXids := state, votes, B, UnallocatedXids;
    Civl_linear_Pair_available := MapOr_5714(Set_Collector_5714(UnallocatedXids), 
      MapOr_5714(Set_Collector_5714(B), MapConst_5_4577(false)));
    goto anon2_LoopDone, anon2_LoopBody;

  anon2_LoopBody:
    goto anon2_LoopBody_0, Civl_NoninterferenceChecker, Civl_UnchangedChecker;

  anon2_LoopBody_0:
    call xid := Civl_ParallelCall_Coordinator_TransactionReq_8();
    Civl_global_old_state, Civl_global_old_votes, Civl_global_old_B, Civl_global_old_UnallocatedXids := state, votes, B, UnallocatedXids;
    Civl_linear_Pair_available := MapOr_5714(Set_Collector_5714(UnallocatedXids), 
      MapOr_5714(Set_Collector_5714(B), MapConst_5_4577(false)));
    assume (exists Civl_partition_Pair: [Pair]int :: 
      MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
           == MapConst_5_4577(true)
         && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
            MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
           == MapConst_5_4577(true));
    goto anon2_LoopHead, Civl_NoninterferenceChecker, Civl_UnchangedChecker;

  anon2_LoopDone:
    goto Civl_ReturnChecker, Civl_UnifiedReturn, Civl_NoninterferenceChecker;

  Civl_NoninterferenceChecker:
    call Civl_Wrapper_NoninterferenceChecker_8(Civl_linear_Pair_available, Civl_global_old_state, Civl_global_old_votes, Civl_global_old_B, Civl_global_old_UnallocatedXids);
    assume false;
    return;

  Civl_RefinementChecker:
    assume false;
    return;

  Civl_UnchangedChecker:
    assume false;
    return;

  Civl_ReturnChecker:
    assume false;
    return;

  Civl_UnifiedReturn:
    return;
}



implementation Civl_Coordinator_TransactionReq_8() returns (xid: int)
{
  var pair: One_6657;
  var pairs: Set_5714;
  var snapshot: [int][int]int;
  var i: int;
  var Civl_global_old_state: [int][int]int;
  var Civl_global_old_votes: [int]int;
  var Civl_global_old_B: Set_5714;
  var Civl_global_old_UnallocatedXids: Set_5714;
  var Civl_linear_Pair_available: [Pair]bool;

  /*** structured program:
    call xid, pairs := AllocateXid();
    call {:layer 10} snapshot := Copy_7021(state);
    i := 1;
    while (i <= numParticipants)
      invariant Inv_8(state, B, votes);
      invariant pairs == Set_5714((lambda p: Pair :: pair(xid, p->mid, p) && i <= p->mid));
      invariant votes[xid] == -1
         || (forall p: Pair :: 
          Set_Contains_4605(pairs, p) ==> UndecidedOrCommitted(state[xid][p->mid]));
      invariant Inv_9(state, B, xid);
      invariant gConsistent(state);
      invariant ExistsMonotoneExtension(snapshot, state, xid);
      invariant 1 <= i && i <= numParticipants + 1;
    {
        call pair := One_Get(pairs, Pair(xid, i));
        async call {:sync} Participant_VoteReq(xid, i, pair);
        i := i + 1;
    }

    assert {:add_to_pool "A", state[xid]} true;
  **** end structured program */

  Civl_init:
    havoc state, votes, B, UnallocatedXids;
    assume (exists Civl_partition_Pair: [Pair]int :: 
      MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
           == MapConst_5_4577(true)
         && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
            MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
           == MapConst_5_4577(true));
    assume Inv_8(state, B, votes);
    Civl_global_old_state, Civl_global_old_votes, Civl_global_old_B, Civl_global_old_UnallocatedXids := state, votes, B, UnallocatedXids;
    Civl_linear_Pair_available := MapOr_5714(Set_Collector_5714(UnallocatedXids), 
      MapOr_5714(Set_Collector_5714(B), MapConst_5_4577(false)));
    goto anon0;

  anon0:
    // <<< injected gate
    assume (forall xid: int :: 
      state[xid] == (lambda j: int :: UNDECIDED())
         ==> 
        Set_IsSubset_4812(perm(xid), UnallocatedXids)
         ==> Set_IsSubset_4812(perm(xid), UnallocatedXids));
    // injected gate >>>
    call xid, pairs := atomic_AllocateXid();
    i := 1;
    goto anon3_LoopHead;

  anon3_LoopHead:
    assume (exists Civl_partition_Pair: [Pair]int :: 
      MapImp_4812(Set_Collector_5714(pairs), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
           == MapConst_5_4577(true)
         && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
           == MapConst_5_4577(true)
         && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
            MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
           == MapConst_5_4577(true));
    assert Inv_8(state, B, votes);
    assert pairs == Set_5714((lambda p: Pair :: pair(xid, p->mid, p) && i <= p->mid));
    assert votes[xid] == -1
       || (forall p: Pair :: 
        Set_Contains_4605(pairs, p) ==> UndecidedOrCommitted(state[xid][p->mid]));
    assert true;
    assert true;
    assert true;
    assert 1 <= i && i <= numParticipants + 1;
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    assume {:partition} i <= numParticipants;
    assert Set_Contains_4605(pairs, Pair(xid, i));
    pairs := Set_Remove_4654(pairs, Pair(xid, i));
    pair := One_6657(Pair(xid, i));
    call {:sync} Civl_AsyncCall_Participant_VoteReq_8(xid, i, pair);
    i := i + 1;
    goto anon3_LoopHead;

  anon3_LoopDone:
    assume {:partition} numParticipants < i;
    goto anon2;

  anon2:
    assert {:add_to_pool "A", state[xid]} true;
    goto Civl_ReturnChecker, Civl_UnifiedReturn, Civl_NoninterferenceChecker;

  Civl_NoninterferenceChecker:
    call Civl_Wrapper_NoninterferenceChecker_8(Civl_linear_Pair_available, Civl_global_old_state, Civl_global_old_votes, Civl_global_old_B, Civl_global_old_UnallocatedXids);
    assume false;
    return;

  Civl_RefinementChecker:
    assume false;
    return;

  Civl_UnchangedChecker:
    assume false;
    return;

  Civl_ReturnChecker:
    assume false;
    return;

  Civl_UnifiedReturn:
    return;
}



implementation Civl_Participant_VoteReq_8(xid: int, mid: int, pair: One_6657)
{
  var Civl_global_old_state: [int][int]int;
  var Civl_global_old_votes: [int]int;
  var Civl_global_old_B: Set_5714;
  var Civl_global_old_UnallocatedXids: Set_5714;
  var Civl_linear_Pair_available: [Pair]bool;

  /*** structured program:
    if (*)
    {
        async call {:sync} Coordinator_VoteYes(xid, mid, pair);
    }
    else
    {
        call SetParticipantAborted(xid, mid, pair);
        async call {:sync} Coordinator_VoteNo(xid, mid, pair);
    }

    assume {:add_to_pool "A", state[xid]} true;
  **** end structured program */

  Civl_init:
    havoc state, votes, B, UnallocatedXids;
    assume (exists Civl_partition_Pair: [Pair]int :: 
      MapImp_4812(One_Collector_6657(pair), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
           == MapConst_5_4577(true)
         && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
           == MapConst_5_4577(true)
         && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
            MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
           == MapConst_5_4577(true));
    assume Inv_8(state, B, votes);
    assume pair(old(xid), old(mid), old(pair)->val)
       && (votes[old(xid)] == -1 || UndecidedOrCommitted(state[old(xid)][old(mid)]));
    Civl_global_old_state, Civl_global_old_votes, Civl_global_old_B, Civl_global_old_UnallocatedXids := state, votes, B, UnallocatedXids;
    Civl_linear_Pair_available := MapOr_5714(Set_Collector_5714(UnallocatedXids), 
      MapOr_5714(Set_Collector_5714(B), 
        MapOr_5714(One_Collector_6657(pair), MapConst_5_4577(false))));
    goto anon0;

  anon0:
    goto anon4_Then, anon4_Else;

  anon4_Else:
    // <<< injected gate
    assume xUndecidedOrAborted(state[xid]);
    assume pair(xid, mid, pair->val);
    // injected gate >>>
    call atomic_SetParticipantAborted(xid, mid, pair);
    call {:sync} Civl_AsyncCall_Coordinator_VoteNo_8(xid, mid, pair);
    goto anon3;

  anon3:
    assume {:add_to_pool "A", state[xid]} true;
    goto Civl_ReturnChecker, Civl_UnifiedReturn, Civl_NoninterferenceChecker;

  anon4_Then:
    call {:sync} Civl_AsyncCall_Coordinator_VoteYes_8(xid, mid, pair);
    goto anon3;

  Civl_NoninterferenceChecker:
    call Civl_Wrapper_NoninterferenceChecker_8(Civl_linear_Pair_available, Civl_global_old_state, Civl_global_old_votes, Civl_global_old_B, Civl_global_old_UnallocatedXids);
    assume false;
    return;

  Civl_RefinementChecker:
    assume false;
    return;

  Civl_UnchangedChecker:
    assume false;
    return;

  Civl_ReturnChecker:
    assume false;
    return;

  Civl_UnifiedReturn:
    return;
}



implementation Civl_Coordinator_VoteYes_8(xid: int, mid: int, pair: One_6657)
{
  var commit: bool;
  var i: int;
  var snapshot: [int][int]int;
  var Civl_global_old_state: [int][int]int;
  var Civl_global_old_votes: [int]int;
  var Civl_global_old_B: Set_5714;
  var Civl_global_old_UnallocatedXids: Set_5714;
  var Civl_pc: bool;
  var Civl_ok: bool;
  var Civl_eval: bool;
  var Civl_linear_Pair_available: [Pair]bool;

  /*** structured program:
    call {:layer 8} snapshot := Copy_7021(state);
    call {:layer 8} Lemma_add_to_set(B->val, pair->val);
    call {:layer 8} Lemma_all_in_set(B->val, xid);
    call commit := StateUpdateOnVoteYes(xid, mid, pair);
    call {:layer 8} Lemma_all_in_set(B->val, xid);
    if (commit)
    {
        assert xUndecidedOrCommitted(snapshot[xid]);
        assert xUndecidedOrCommitted(state[xid]);
        i := 1;
        while (i <= numParticipants)
          invariant 1 <= i && i <= numParticipants + 1;
          invariant Inv_8(state, B, votes);
          invariant ExistsMonotoneExtension(snapshot, state, xid);
        {
            async call {:sync} Participant_Commit(xid, i);
            i := i + 1;
        }
    }

    assert {:add_to_pool "A", state[xid]} true;
  **** end structured program */

  Civl_init:
    havoc state, votes, B, UnallocatedXids;
    assume (exists Civl_partition_Pair: [Pair]int :: 
      MapImp_4812(One_Collector_6657(pair), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
           == MapConst_5_4577(true)
         && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
           == MapConst_5_4577(true)
         && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
            MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
           == MapConst_5_4577(true));
    assume Inv_8(state, B, votes);
    assume pair(old(xid), old(mid), old(pair)->val)
       && (votes[old(xid)] == -1 || UndecidedOrCommitted(state[old(xid)][old(mid)]));
    Civl_global_old_state, Civl_global_old_votes, Civl_global_old_B, Civl_global_old_UnallocatedXids := state, votes, B, UnallocatedXids;
    Civl_pc, Civl_ok, Civl_eval := false, false, false;
    assume xConsistent(state[xid])
       && pair(xid, mid, pair->val)
       && Set_IsDisjoint_4577(perm(xid), UnallocatedXids);
    Civl_linear_Pair_available := MapOr_5714(Set_Collector_5714(UnallocatedXids), 
      MapOr_5714(Set_Collector_5714(B), 
        MapOr_5714(One_Collector_6657(pair), MapConst_5_4577(false))));
    goto anon0;

  anon0:
    call {:layer 8} snapshot := Copy_7021(state);
    call {:layer 8} Lemma_add_to_set(B->val, pair->val);
    call {:layer 8} Lemma_all_in_set(B->val, xid);
    // <<< injected gate
    assert VotesEqCoordinatorState(votes, state, xid);
    assert Set_IsDisjoint_4577(perm(xid), UnallocatedXids);
    // injected gate >>>
    call commit := atomic_StateUpdateOnVoteYes(xid, mid, pair);
    call {:layer 8} Lemma_all_in_set(B->val, xid);
    goto anon4_Then, anon4_Else;

  anon4_Else:
    assume {:partition} !commit;
    goto anon3;

  anon3:
    assert {:add_to_pool "A", state[xid]} true;
    goto Civl_ReturnChecker, Civl_UnifiedReturn, Civl_NoninterferenceChecker;

  anon4_Then:
    assume {:partition} commit;
    assert xUndecidedOrCommitted(snapshot[xid]);
    assert xUndecidedOrCommitted(state[xid]);
    i := 1;
    goto anon5_LoopHead;

  anon5_LoopHead:
    assume (exists Civl_partition_Pair: [Pair]int :: 
      MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
           == MapConst_5_4577(true)
         && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
            MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
           == MapConst_5_4577(true));
    assert 1 <= i && i <= numParticipants + 1;
    assert Inv_8(state, B, votes);
    assert ExistsMonotoneExtension(snapshot, state, xid);
    goto anon5_LoopDone, anon5_LoopBody;

  anon5_LoopBody:
    assume {:partition} i <= numParticipants;
    // <<< injected gate
    assert Committed(state[xid][CoordinatorMid]);
    assert xUndecidedOrCommitted(state[xid]);
    assert participantMid(i);
    // injected gate >>>
    call {:sync} atomic_Participant_Commit(xid, i);
    i := i + 1;
    goto anon5_LoopHead;

  anon5_LoopDone:
    assume {:partition} numParticipants < i;
    goto anon3;

  Civl_NoninterferenceChecker:
    call Civl_Wrapper_NoninterferenceChecker_8(Civl_linear_Pair_available, Civl_global_old_state, Civl_global_old_votes, Civl_global_old_B, Civl_global_old_UnallocatedXids);
    assume false;
    return;

  Civl_RefinementChecker:
    assert Civl_pc
       || 
      (
        state == Civl_global_old_state
         && B == Civl_global_old_B
         && UnallocatedXids == Civl_global_old_UnallocatedXids)
       || Civl_eval;
    assert Civl_pc
       ==> state == Civl_global_old_state
         && B == Civl_global_old_B
         && UnallocatedXids == Civl_global_old_UnallocatedXids;
    assume false;
    return;

  Civl_UnchangedChecker:
    assert state == Civl_global_old_state
       && B == Civl_global_old_B
       && UnallocatedXids == Civl_global_old_UnallocatedXids;
    assert Civl_pc ==> true;
    assume false;
    return;

  Civl_ReturnChecker:
    Civl_eval := (exists {:pool "A"} Civl_x#0: [int]int :: 
        xAllParticipantsInB(xid, B)
           && xConsistentExtension(Civl_global_old_state[xid], state[xid])
           && B == Set_Add_4588(Civl_global_old_B, pair->val)
           && state == Civl_global_old_state[xid := Civl_x#0]
           && UnallocatedXids == Civl_global_old_UnallocatedXids)
       || (
        B == Set_Add_4588(Civl_global_old_B, pair->val)
         && state == Civl_global_old_state
         && UnallocatedXids == Civl_global_old_UnallocatedXids);
    assert Civl_pc
       || 
      (
        state == Civl_global_old_state
         && B == Civl_global_old_B
         && UnallocatedXids == Civl_global_old_UnallocatedXids)
       || Civl_eval;
    assert Civl_pc
       ==> state == Civl_global_old_state
         && B == Civl_global_old_B
         && UnallocatedXids == Civl_global_old_UnallocatedXids;
    Civl_pc, Civl_ok := state == Civl_global_old_state
         && B == Civl_global_old_B
         && UnallocatedXids == Civl_global_old_UnallocatedXids
       ==> Civl_pc, Civl_eval || Civl_ok;
    assert Civl_ok;
    assume false;
    return;

  Civl_UnifiedReturn:
    return;
}



implementation Civl_Coordinator_VoteNo_8(xid: int, mid: int, pair: One_6657)
{
  var abort: bool;
  var i: int;
  var snapshot: [int][int]int;
  var Civl_global_old_state: [int][int]int;
  var Civl_global_old_votes: [int]int;
  var Civl_global_old_B: Set_5714;
  var Civl_global_old_UnallocatedXids: Set_5714;
  var Civl_pc: bool;
  var Civl_ok: bool;
  var Civl_eval: bool;
  var Civl_linear_Pair_available: [Pair]bool;

  /*** structured program:
    call {:layer 8} snapshot := Copy_7021(state);
    call abort := StateUpdateOnVoteNo(xid, mid);
    if (abort)
    {
        i := 1;
        while (i <= numParticipants)
          invariant 1 <= i && i <= numParticipants + 1;
          invariant Aborted(state[xid][CoordinatorMid]);
          invariant xUndecidedOrAborted(state[xid]);
          invariant ExistsMonotoneExtension(snapshot, state, xid);
        {
            async call {:sync} Participant_Abort(xid, i);
            i := i + 1;
        }
    }

    assert {:add_to_pool "A", state[xid]} true;
  **** end structured program */

  Civl_init:
    havoc state, votes, B, UnallocatedXids;
    assume (exists Civl_partition_Pair: [Pair]int :: 
      MapImp_4812(One_Collector_6657(pair), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
           == MapConst_5_4577(true)
         && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
           == MapConst_5_4577(true)
         && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
            MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
           == MapConst_5_4577(true));
    assume pair(old(xid), old(mid), old(pair)->val) && Aborted(state[old(xid)][old(mid)]);
    Civl_global_old_state, Civl_global_old_votes, Civl_global_old_B, Civl_global_old_UnallocatedXids := state, votes, B, UnallocatedXids;
    Civl_pc, Civl_ok, Civl_eval := false, false, false;
    assume xUndecidedOrAborted(state[xid])
       && pair(xid, mid, pair->val)
       && Set_IsDisjoint_4577(perm(xid), UnallocatedXids);
    Civl_linear_Pair_available := MapOr_5714(Set_Collector_5714(UnallocatedXids), 
      MapOr_5714(Set_Collector_5714(B), 
        MapOr_5714(One_Collector_6657(pair), MapConst_5_4577(false))));
    goto anon0;

  anon0:
    call {:layer 8} snapshot := Copy_7021(state);
    // <<< injected gate
    assert !Committed(state[xid][CoordinatorMid]);
    assert Set_IsDisjoint_4577(perm(xid), UnallocatedXids);
    // injected gate >>>
    call abort := atomic_StateUpdateOnVoteNo(xid, mid);
    goto anon4_Then, anon4_Else;

  anon4_Else:
    assume {:partition} !abort;
    goto anon3;

  anon3:
    assert {:add_to_pool "A", state[xid]} true;
    goto Civl_ReturnChecker, Civl_UnifiedReturn, Civl_NoninterferenceChecker;

  anon4_Then:
    assume {:partition} abort;
    i := 1;
    goto anon5_LoopHead;

  anon5_LoopHead:
    assume (exists Civl_partition_Pair: [Pair]int :: 
      MapImp_4812(One_Collector_6657(pair), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
           == MapConst_5_4577(true)
         && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
           == MapConst_5_4577(true)
         && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
            MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
           == MapConst_5_4577(true));
    assert 1 <= i && i <= numParticipants + 1;
    assert Aborted(state[xid][CoordinatorMid]);
    assert xUndecidedOrAborted(state[xid]);
    assert ExistsMonotoneExtension(snapshot, state, xid);
    goto anon5_LoopDone, anon5_LoopBody;

  anon5_LoopBody:
    assume {:partition} i <= numParticipants;
    // <<< injected gate
    assert Aborted(state[xid][CoordinatorMid]);
    assert xUndecidedOrAborted(state[xid]);
    assert participantMid(i);
    // injected gate >>>
    call {:sync} atomic_Participant_Abort(xid, i);
    i := i + 1;
    goto anon5_LoopHead;

  anon5_LoopDone:
    assume {:partition} numParticipants < i;
    goto anon3;

  Civl_NoninterferenceChecker:
    call Civl_Wrapper_NoninterferenceChecker_8(Civl_linear_Pair_available, Civl_global_old_state, Civl_global_old_votes, Civl_global_old_B, Civl_global_old_UnallocatedXids);
    assume false;
    return;

  Civl_RefinementChecker:
    assert Civl_pc
       || 
      (
        state == Civl_global_old_state
         && B == Civl_global_old_B
         && UnallocatedXids == Civl_global_old_UnallocatedXids)
       || Civl_eval;
    assert Civl_pc
       ==> state == Civl_global_old_state
         && B == Civl_global_old_B
         && UnallocatedXids == Civl_global_old_UnallocatedXids;
    assume false;
    return;

  Civl_UnchangedChecker:
    assert state == Civl_global_old_state
       && B == Civl_global_old_B
       && UnallocatedXids == Civl_global_old_UnallocatedXids;
    assert Civl_pc ==> true;
    assume false;
    return;

  Civl_ReturnChecker:
    Civl_eval := (exists {:pool "A"} Civl_x#0: [int]int :: 
      xUndecidedOrAborted(state[xid])
         && xConsistentExtension(Civl_global_old_state[xid], state[xid])
         && state == Civl_global_old_state[xid := Civl_x#0]
         && B == Civl_global_old_B
         && UnallocatedXids == Civl_global_old_UnallocatedXids);
    assert Civl_pc
       || 
      (
        state == Civl_global_old_state
         && B == Civl_global_old_B
         && UnallocatedXids == Civl_global_old_UnallocatedXids)
       || Civl_eval;
    assert Civl_pc
       ==> state == Civl_global_old_state
         && B == Civl_global_old_B
         && UnallocatedXids == Civl_global_old_UnallocatedXids;
    Civl_pc, Civl_ok := state == Civl_global_old_state
         && B == Civl_global_old_B
         && UnallocatedXids == Civl_global_old_UnallocatedXids
       ==> Civl_pc, Civl_eval || Civl_ok;
    assert Civl_ok;
    assume false;
    return;

  Civl_UnifiedReturn:
    return;
}



procedure Civl_AsyncCall_Participant_VoteReq_8(xid: int, mid: int, pair: One_6657);
  requires Inv_8(state, B, votes);
  requires pair(xid, mid, pair->val)
     && (votes[xid] == -1 || UndecidedOrCommitted(state[xid][mid]));



procedure Civl_AsyncCall_Coordinator_VoteNo_8(xid: int, mid: int, pair: One_6657);
  requires pair(xid, mid, pair->val) && Aborted(state[xid][mid]);



procedure Civl_AsyncCall_Coordinator_VoteYes_8(xid: int, mid: int, pair: One_6657);
  requires Inv_8(state, B, votes);
  requires pair(xid, mid, pair->val)
     && (votes[xid] == -1 || UndecidedOrCommitted(state[xid][mid]));



procedure {:inline 1} Civl_NoninterferenceChecker_yield_YieldInv_8(Civl_linear_Pair_in: [Pair]bool, 
    Civl_snapshot_state: [int][int]int, 
    Civl_snapshot_votes: [int]int, 
    Civl_snapshot_B: Set_5714, 
    Civl_snapshot_UnallocatedXids: Set_5714);



implementation Civl_NoninterferenceChecker_yield_YieldInv_8(Civl_linear_Pair_in: [Pair]bool, 
    Civl_snapshot_state: [int][int]int, 
    Civl_snapshot_votes: [int]int, 
    Civl_snapshot_B: Set_5714, 
    Civl_snapshot_UnallocatedXids: Set_5714)
{

  enter:
    goto exit, L;

  exit:
    return;

  L:
    assume Inv_8(Civl_snapshot_state, Civl_snapshot_B, Civl_snapshot_votes);
    assert Inv_8(state, B, votes);
    assume false;
    return;
}



procedure {:inline 1} Civl_NoninterferenceChecker_yield_YieldUndecidedOrCommitted_8(Civl_linear_Pair_in: [Pair]bool, 
    Civl_snapshot_state: [int][int]int, 
    Civl_snapshot_votes: [int]int, 
    Civl_snapshot_B: Set_5714, 
    Civl_snapshot_UnallocatedXids: Set_5714);



implementation Civl_NoninterferenceChecker_yield_YieldUndecidedOrCommitted_8(Civl_linear_Pair_in: [Pair]bool, 
    Civl_snapshot_state: [int][int]int, 
    Civl_snapshot_votes: [int]int, 
    Civl_snapshot_B: Set_5714, 
    Civl_snapshot_UnallocatedXids: Set_5714)
{
  var xid: int;
  var mid: int;
  var pair: One_6657;

  enter:
    goto exit, L;

  exit:
    return;

  L:
    assume (exists Civl_partition_Pair: [Pair]int :: 
      MapImp_4812(One_Collector_6657(pair), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
           == MapConst_5_4577(true)
         && MapImp_4812(Civl_linear_Pair_in, MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
           == MapConst_5_4577(true));
    assume pair(xid, mid, pair->val)
       && (Civl_snapshot_votes[xid] == -1
         || UndecidedOrCommitted(Civl_snapshot_state[xid][mid]));
    assert pair(xid, mid, pair->val)
       && (votes[xid] == -1 || UndecidedOrCommitted(state[xid][mid]));
    assume false;
    return;
}



procedure {:inline 1} Civl_NoninterferenceChecker_yield_YieldAborted_8(Civl_linear_Pair_in: [Pair]bool, 
    Civl_snapshot_state: [int][int]int, 
    Civl_snapshot_votes: [int]int, 
    Civl_snapshot_B: Set_5714, 
    Civl_snapshot_UnallocatedXids: Set_5714);



implementation Civl_NoninterferenceChecker_yield_YieldAborted_8(Civl_linear_Pair_in: [Pair]bool, 
    Civl_snapshot_state: [int][int]int, 
    Civl_snapshot_votes: [int]int, 
    Civl_snapshot_B: Set_5714, 
    Civl_snapshot_UnallocatedXids: Set_5714)
{
  var xid: int;
  var mid: int;
  var pair: One_6657;

  enter:
    goto exit, L;

  exit:
    return;

  L:
    assume (exists Civl_partition_Pair: [Pair]int :: 
      MapImp_4812(One_Collector_6657(pair), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
           == MapConst_5_4577(true)
         && MapImp_4812(Civl_linear_Pair_in, MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
           == MapConst_5_4577(true));
    assume pair(xid, mid, pair->val) && Aborted(Civl_snapshot_state[xid][mid]);
    assert pair(xid, mid, pair->val) && Aborted(state[xid][mid]);
    assume false;
    return;
}



procedure Civl_ParallelCall_Coordinator_TransactionReq_8() returns (Civl_0_xid: int);
  requires Inv_8(state, B, votes);
  modifies state, votes, B, UnallocatedXids;
  ensures Inv_8(state, B, votes);



procedure {:inline 1} Civl_Wrapper_NoninterferenceChecker_8(Civl_linear_Pair_in: [Pair]bool, 
    Civl_global_old_state: [int][int]int, 
    Civl_global_old_votes: [int]int, 
    Civl_global_old_B: Set_5714, 
    Civl_global_old_UnallocatedXids: Set_5714);



implementation Civl_Wrapper_NoninterferenceChecker_8(Civl_Civl_linear_Pair_in: [Pair]bool, 
    Civl_Civl_global_old_state: [int][int]int, 
    Civl_Civl_global_old_votes: [int]int, 
    Civl_Civl_global_old_B: Set_5714, 
    Civl_Civl_global_old_UnallocatedXids: Set_5714)
{

  enter:
    goto L_0, L_1, L_2;

  L_0:
    call Civl_NoninterferenceChecker_yield_YieldInv_8(Civl_Civl_linear_Pair_in, Civl_Civl_global_old_state, Civl_Civl_global_old_votes, Civl_Civl_global_old_B, Civl_Civl_global_old_UnallocatedXids);
    return;

  L_1:
    call Civl_NoninterferenceChecker_yield_YieldUndecidedOrCommitted_8(Civl_Civl_linear_Pair_in, Civl_Civl_global_old_state, Civl_Civl_global_old_votes, Civl_Civl_global_old_B, Civl_Civl_global_old_UnallocatedXids);
    return;

  L_2:
    call Civl_NoninterferenceChecker_yield_YieldAborted_8(Civl_Civl_linear_Pair_in, Civl_Civl_global_old_state, Civl_Civl_global_old_votes, Civl_Civl_global_old_B, Civl_Civl_global_old_UnallocatedXids);
    return;
}



procedure Civl_main_9();
  requires gConsistent(state);
  modifies state, votes, B, UnallocatedXids;



procedure Civl_Coordinator_TransactionReq_9() returns (xid: int);
  requires gConsistent(state);
  modifies state, votes, B, UnallocatedXids;
  ensures gConsistent(state);



procedure Civl_Participant_VoteReq_9(xid: int, mid: int, pair: One_6657);
  requires Inv_9(state, B, xid);
  modifies state, votes, B, UnallocatedXids;



implementation Civl_main_9()
{
  var xid: int;
  var Civl_global_old_state: [int][int]int;
  var Civl_global_old_votes: [int]int;
  var Civl_global_old_B: Set_5714;
  var Civl_global_old_UnallocatedXids: Set_5714;
  var Civl_linear_Pair_available: [Pair]bool;

  /*** structured program:
    while (*)
      invariant      call YieldInv_8();
      invariant      call YieldConsistent_9();
      invariant      call YieldConsistent_10();
      invariant {:yields} true;
    {
        call xid := Coordinator_TransactionReq();
    }
  **** end structured program */

  Civl_init:
    havoc state, votes, B, UnallocatedXids;
    assume (exists Civl_partition_Pair: [Pair]int :: 
      MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
           == MapConst_5_4577(true)
         && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
            MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
           == MapConst_5_4577(true));
    assume gConsistent(state);
    Civl_global_old_state, Civl_global_old_votes, Civl_global_old_B, Civl_global_old_UnallocatedXids := state, votes, B, UnallocatedXids;
    Civl_linear_Pair_available := MapOr_5714(Set_Collector_5714(UnallocatedXids), 
      MapOr_5714(Set_Collector_5714(B), MapConst_5_4577(false)));
    goto anon0;

  anon0:
    goto anon2_LoopHead, Civl_NoninterferenceChecker, Civl_RefinementChecker;

  anon2_LoopHead:
    assume (exists Civl_partition_Pair: [Pair]int :: 
      MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
           == MapConst_5_4577(true)
         && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
            MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
           == MapConst_5_4577(true));
    assert gConsistent(state);
    state, votes, B, UnallocatedXids := state, votes, B, UnallocatedXids;
    Civl_global_old_state, Civl_global_old_votes, Civl_global_old_B, Civl_global_old_UnallocatedXids := state, votes, B, UnallocatedXids;
    Civl_linear_Pair_available := MapOr_5714(Set_Collector_5714(UnallocatedXids), 
      MapOr_5714(Set_Collector_5714(B), MapConst_5_4577(false)));
    goto anon2_LoopDone, anon2_LoopBody;

  anon2_LoopBody:
    goto anon2_LoopBody_0, Civl_NoninterferenceChecker, Civl_UnchangedChecker;

  anon2_LoopBody_0:
    call xid := Civl_ParallelCall_Coordinator_TransactionReq_9();
    Civl_global_old_state, Civl_global_old_votes, Civl_global_old_B, Civl_global_old_UnallocatedXids := state, votes, B, UnallocatedXids;
    Civl_linear_Pair_available := MapOr_5714(Set_Collector_5714(UnallocatedXids), 
      MapOr_5714(Set_Collector_5714(B), MapConst_5_4577(false)));
    assume (exists Civl_partition_Pair: [Pair]int :: 
      MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
           == MapConst_5_4577(true)
         && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
            MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
           == MapConst_5_4577(true));
    goto anon2_LoopHead, Civl_NoninterferenceChecker, Civl_UnchangedChecker;

  anon2_LoopDone:
    goto Civl_ReturnChecker, Civl_UnifiedReturn, Civl_NoninterferenceChecker;

  Civl_NoninterferenceChecker:
    call Civl_Wrapper_NoninterferenceChecker_9(Civl_linear_Pair_available, Civl_global_old_state, Civl_global_old_votes, Civl_global_old_B, Civl_global_old_UnallocatedXids);
    assume false;
    return;

  Civl_RefinementChecker:
    assume false;
    return;

  Civl_UnchangedChecker:
    assume false;
    return;

  Civl_ReturnChecker:
    assume false;
    return;

  Civl_UnifiedReturn:
    return;
}



implementation Civl_Coordinator_TransactionReq_9() returns (xid: int)
{
  var pair: One_6657;
  var pairs: Set_5714;
  var snapshot: [int][int]int;
  var i: int;
  var Civl_global_old_state: [int][int]int;
  var Civl_global_old_votes: [int]int;
  var Civl_global_old_B: Set_5714;
  var Civl_global_old_UnallocatedXids: Set_5714;
  var Civl_linear_Pair_available: [Pair]bool;

  /*** structured program:
    call xid, pairs := AllocateXid();
    call {:layer 10} snapshot := Copy_7021(state);
    i := 1;
    while (i <= numParticipants)
      invariant Inv_8(state, B, votes);
      invariant pairs == Set_5714((lambda p: Pair :: pair(xid, p->mid, p) && i <= p->mid));
      invariant votes[xid] == -1
         || (forall p: Pair :: 
          Set_Contains_4605(pairs, p) ==> UndecidedOrCommitted(state[xid][p->mid]));
      invariant Inv_9(state, B, xid);
      invariant gConsistent(state);
      invariant ExistsMonotoneExtension(snapshot, state, xid);
      invariant 1 <= i && i <= numParticipants + 1;
    {
        call pair := One_Get(pairs, Pair(xid, i));
        async call {:sync} Participant_VoteReq(xid, i, pair);
        i := i + 1;
    }

    assert {:add_to_pool "A", state[xid]} true;
  **** end structured program */

  Civl_init:
    havoc state, votes, B, UnallocatedXids;
    assume (exists Civl_partition_Pair: [Pair]int :: 
      MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
           == MapConst_5_4577(true)
         && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
            MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
           == MapConst_5_4577(true));
    assume gConsistent(state);
    Civl_global_old_state, Civl_global_old_votes, Civl_global_old_B, Civl_global_old_UnallocatedXids := state, votes, B, UnallocatedXids;
    Civl_linear_Pair_available := MapOr_5714(Set_Collector_5714(UnallocatedXids), 
      MapOr_5714(Set_Collector_5714(B), MapConst_5_4577(false)));
    goto anon0;

  anon0:
    // <<< injected gate
    assume (forall xid: int :: 
      state[xid] == (lambda j: int :: UNDECIDED())
         ==> 
        Set_IsSubset_4812(perm(xid), UnallocatedXids)
         ==> Set_IsSubset_4812(perm(xid), UnallocatedXids));
    // injected gate >>>
    call xid, pairs := atomic_AllocateXid();
    i := 1;
    goto anon3_LoopHead;

  anon3_LoopHead:
    assume (exists Civl_partition_Pair: [Pair]int :: 
      MapImp_4812(Set_Collector_5714(pairs), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
           == MapConst_5_4577(true)
         && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
           == MapConst_5_4577(true)
         && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
            MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
           == MapConst_5_4577(true));
    assert true;
    assert pairs == Set_5714((lambda p: Pair :: pair(xid, p->mid, p) && i <= p->mid));
    assert true;
    assert Inv_9(state, B, xid);
    assert true;
    assert true;
    assert 1 <= i && i <= numParticipants + 1;
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    assume {:partition} i <= numParticipants;
    assert Set_Contains_4605(pairs, Pair(xid, i));
    pairs := Set_Remove_4654(pairs, Pair(xid, i));
    pair := One_6657(Pair(xid, i));
    call {:sync} Civl_AsyncCall_Participant_VoteReq_9(xid, i, pair);
    i := i + 1;
    goto anon3_LoopHead;

  anon3_LoopDone:
    assume {:partition} numParticipants < i;
    goto anon2;

  anon2:
    assert {:add_to_pool "A", state[xid]} true;
    goto Civl_ReturnChecker, Civl_UnifiedReturn, Civl_NoninterferenceChecker;

  Civl_NoninterferenceChecker:
    call Civl_Wrapper_NoninterferenceChecker_9(Civl_linear_Pair_available, Civl_global_old_state, Civl_global_old_votes, Civl_global_old_B, Civl_global_old_UnallocatedXids);
    assume false;
    return;

  Civl_RefinementChecker:
    assume false;
    return;

  Civl_UnchangedChecker:
    assume false;
    return;

  Civl_ReturnChecker:
    assume false;
    return;

  Civl_UnifiedReturn:
    return;
}



implementation Civl_Participant_VoteReq_9(xid: int, mid: int, pair: One_6657)
{
  var Civl_global_old_state: [int][int]int;
  var Civl_global_old_votes: [int]int;
  var Civl_global_old_B: Set_5714;
  var Civl_global_old_UnallocatedXids: Set_5714;
  var Civl_pc: bool;
  var Civl_ok: bool;
  var Civl_eval: bool;
  var Civl_linear_Pair_available: [Pair]bool;

  /*** structured program:
    if (*)
    {
        async call {:sync} Coordinator_VoteYes(xid, mid, pair);
    }
    else
    {
        call SetParticipantAborted(xid, mid, pair);
        async call {:sync} Coordinator_VoteNo(xid, mid, pair);
    }

    assume {:add_to_pool "A", state[xid]} true;
  **** end structured program */

  Civl_init:
    havoc state, votes, B, UnallocatedXids;
    assume (exists Civl_partition_Pair: [Pair]int :: 
      MapImp_4812(One_Collector_6657(pair), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
           == MapConst_5_4577(true)
         && MapImp_4812(Set_Collector_5714(B), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
           == MapConst_5_4577(true)
         && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
            MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(2)))
           == MapConst_5_4577(true));
    assume Inv_9(state, B, old(xid));
    Civl_global_old_state, Civl_global_old_votes, Civl_global_old_B, Civl_global_old_UnallocatedXids := state, votes, B, UnallocatedXids;
    Civl_pc, Civl_ok, Civl_eval := false, false, false;
    assume xConsistent(state[xid])
       && pair(xid, mid, pair->val)
       && Set_IsDisjoint_4577(perm(xid), UnallocatedXids);
    Civl_linear_Pair_available := MapOr_5714(Set_Collector_5714(UnallocatedXids), 
      MapOr_5714(Set_Collector_5714(B), 
        MapOr_5714(One_Collector_6657(pair), MapConst_5_4577(false))));
    goto anon0;

  anon0:
    goto anon4_Then, anon4_Else;

  anon4_Else:
    // <<< injected gate
    assert xUndecidedOrAborted(state[xid]);
    assert pair(xid, mid, pair->val);
    // injected gate >>>
    call atomic_SetParticipantAborted(xid, mid, pair);
    // <<< injected gate
    assert xUndecidedOrAborted(state[xid]);
    assert pair(xid, mid, pair->val);
    assert Set_IsDisjoint_4577(perm(xid), UnallocatedXids);
    // injected gate >>>
    call {:sync} atomic_Coordinator_VoteNo(xid, mid, pair);
    goto anon3;

  anon3:
    assume {:add_to_pool "A", state[xid]} true;
    goto Civl_ReturnChecker, Civl_UnifiedReturn, Civl_NoninterferenceChecker;

  anon4_Then:
    // <<< injected gate
    assert xConsistent(state[xid]);
    assert pair(xid, mid, pair->val);
    assert Set_IsDisjoint_4577(perm(xid), UnallocatedXids);
    // injected gate >>>
    call {:sync} atomic_Coordinator_VoteYes(xid, mid, pair);
    goto anon3;

  Civl_NoninterferenceChecker:
    call Civl_Wrapper_NoninterferenceChecker_9(Civl_linear_Pair_available, Civl_global_old_state, Civl_global_old_votes, Civl_global_old_B, Civl_global_old_UnallocatedXids);
    assume false;
    return;

  Civl_RefinementChecker:
    assert Civl_pc
       || 
      (state == Civl_global_old_state
         && UnallocatedXids == Civl_global_old_UnallocatedXids)
       || Civl_eval;
    assert Civl_pc
       ==> state == Civl_global_old_state
         && UnallocatedXids == Civl_global_old_UnallocatedXids;
    assume false;
    return;

  Civl_UnchangedChecker:
    assert state == Civl_global_old_state
       && UnallocatedXids == Civl_global_old_UnallocatedXids;
    assert Civl_pc ==> true;
    assume false;
    return;

  Civl_ReturnChecker:
    Civl_eval := (exists {:pool "A"} Civl_x#0: [int]int :: 
      xConsistentExtension(Civl_global_old_state[xid], state[xid])
         && state == Civl_global_old_state[xid := Civl_x#0]
         && UnallocatedXids == Civl_global_old_UnallocatedXids);
    assert Civl_pc
       || 
      (state == Civl_global_old_state
         && UnallocatedXids == Civl_global_old_UnallocatedXids)
       || Civl_eval;
    assert Civl_pc
       ==> state == Civl_global_old_state
         && UnallocatedXids == Civl_global_old_UnallocatedXids;
    Civl_pc, Civl_ok := state == Civl_global_old_state
         && UnallocatedXids == Civl_global_old_UnallocatedXids
       ==> Civl_pc, Civl_eval || Civl_ok;
    assert Civl_ok;
    assume false;
    return;

  Civl_UnifiedReturn:
    return;
}



procedure Civl_AsyncCall_Participant_VoteReq_9(xid: int, mid: int, pair: One_6657);
  requires Inv_9(state, B, xid);



procedure {:inline 1} Civl_NoninterferenceChecker_yield_YieldInv_9(Civl_linear_Pair_in: [Pair]bool, 
    Civl_snapshot_state: [int][int]int, 
    Civl_snapshot_votes: [int]int, 
    Civl_snapshot_B: Set_5714, 
    Civl_snapshot_UnallocatedXids: Set_5714);



implementation Civl_NoninterferenceChecker_yield_YieldInv_9(Civl_linear_Pair_in: [Pair]bool, 
    Civl_snapshot_state: [int][int]int, 
    Civl_snapshot_votes: [int]int, 
    Civl_snapshot_B: Set_5714, 
    Civl_snapshot_UnallocatedXids: Set_5714)
{
  var xid: int;

  enter:
    goto exit, L;

  exit:
    return;

  L:
    assume Inv_9(Civl_snapshot_state, Civl_snapshot_B, xid);
    assert Inv_9(state, B, xid);
    assume false;
    return;
}



procedure {:inline 1} Civl_NoninterferenceChecker_yield_YieldConsistent_9(Civl_linear_Pair_in: [Pair]bool, 
    Civl_snapshot_state: [int][int]int, 
    Civl_snapshot_votes: [int]int, 
    Civl_snapshot_B: Set_5714, 
    Civl_snapshot_UnallocatedXids: Set_5714);



implementation Civl_NoninterferenceChecker_yield_YieldConsistent_9(Civl_linear_Pair_in: [Pair]bool, 
    Civl_snapshot_state: [int][int]int, 
    Civl_snapshot_votes: [int]int, 
    Civl_snapshot_B: Set_5714, 
    Civl_snapshot_UnallocatedXids: Set_5714)
{

  enter:
    goto exit, L;

  exit:
    return;

  L:
    assume gConsistent(Civl_snapshot_state);
    assert gConsistent(state);
    assume false;
    return;
}



procedure Civl_ParallelCall_Coordinator_TransactionReq_9() returns (Civl_0_xid: int);
  requires gConsistent(state);
  modifies state, votes, B, UnallocatedXids;
  ensures gConsistent(state);



procedure {:inline 1} Civl_Wrapper_NoninterferenceChecker_9(Civl_linear_Pair_in: [Pair]bool, 
    Civl_global_old_state: [int][int]int, 
    Civl_global_old_votes: [int]int, 
    Civl_global_old_B: Set_5714, 
    Civl_global_old_UnallocatedXids: Set_5714);



implementation Civl_Wrapper_NoninterferenceChecker_9(Civl_Civl_linear_Pair_in: [Pair]bool, 
    Civl_Civl_global_old_state: [int][int]int, 
    Civl_Civl_global_old_votes: [int]int, 
    Civl_Civl_global_old_B: Set_5714, 
    Civl_Civl_global_old_UnallocatedXids: Set_5714)
{

  enter:
    goto L_0, L_1;

  L_0:
    call Civl_NoninterferenceChecker_yield_YieldInv_9(Civl_Civl_linear_Pair_in, Civl_Civl_global_old_state, Civl_Civl_global_old_votes, Civl_Civl_global_old_B, Civl_Civl_global_old_UnallocatedXids);
    return;

  L_1:
    call Civl_NoninterferenceChecker_yield_YieldConsistent_9(Civl_Civl_linear_Pair_in, Civl_Civl_global_old_state, Civl_Civl_global_old_votes, Civl_Civl_global_old_B, Civl_Civl_global_old_UnallocatedXids);
    return;
}



procedure Civl_main_10();
  requires gConsistent(state);
  modifies state, votes, B, UnallocatedXids;



procedure Civl_Coordinator_TransactionReq_10() returns (xid: int);
  requires gConsistent(state);
  modifies state, votes, B, UnallocatedXids;
  ensures gConsistent(state);



implementation Civl_main_10()
{
  var xid: int;
  var Civl_global_old_state: [int][int]int;
  var Civl_global_old_votes: [int]int;
  var Civl_global_old_B: Set_5714;
  var Civl_global_old_UnallocatedXids: Set_5714;
  var Civl_linear_Pair_available: [Pair]bool;

  /*** structured program:
    while (*)
      invariant      call YieldInv_8();
      invariant      call YieldConsistent_9();
      invariant      call YieldConsistent_10();
      invariant {:yields} true;
    {
        call xid := Coordinator_TransactionReq();
    }
  **** end structured program */

  Civl_init:
    havoc state, votes, B, UnallocatedXids;
    assume gConsistent(state);
    Civl_global_old_state, Civl_global_old_votes, Civl_global_old_B, Civl_global_old_UnallocatedXids := state, votes, B, UnallocatedXids;
    Civl_linear_Pair_available := MapOr_5714(Set_Collector_5714(UnallocatedXids), MapConst_5_4577(false));
    goto anon0;

  anon0:
    goto anon2_LoopHead, Civl_NoninterferenceChecker, Civl_RefinementChecker;

  anon2_LoopHead:
    assert gConsistent(state);
    state, votes, B, UnallocatedXids := state, votes, B, UnallocatedXids;
    Civl_global_old_state, Civl_global_old_votes, Civl_global_old_B, Civl_global_old_UnallocatedXids := state, votes, B, UnallocatedXids;
    Civl_linear_Pair_available := MapOr_5714(Set_Collector_5714(UnallocatedXids), MapConst_5_4577(false));
    goto anon2_LoopDone, anon2_LoopBody;

  anon2_LoopBody:
    goto anon2_LoopBody_0, Civl_NoninterferenceChecker, Civl_UnchangedChecker;

  anon2_LoopBody_0:
    call xid := Civl_ParallelCall_Coordinator_TransactionReq_10();
    Civl_global_old_state, Civl_global_old_votes, Civl_global_old_B, Civl_global_old_UnallocatedXids := state, votes, B, UnallocatedXids;
    Civl_linear_Pair_available := MapOr_5714(Set_Collector_5714(UnallocatedXids), MapConst_5_4577(false));
    goto anon2_LoopHead, Civl_NoninterferenceChecker, Civl_UnchangedChecker;

  anon2_LoopDone:
    goto Civl_ReturnChecker, Civl_UnifiedReturn, Civl_NoninterferenceChecker;

  Civl_NoninterferenceChecker:
    call Civl_Wrapper_NoninterferenceChecker_10(Civl_linear_Pair_available, Civl_global_old_state, Civl_global_old_votes, Civl_global_old_B, Civl_global_old_UnallocatedXids);
    assume false;
    return;

  Civl_RefinementChecker:
    assume false;
    return;

  Civl_UnchangedChecker:
    assume false;
    return;

  Civl_ReturnChecker:
    assume false;
    return;

  Civl_UnifiedReturn:
    return;
}



implementation Civl_Coordinator_TransactionReq_10() returns (xid: int)
{
  var pair: One_6657;
  var pairs: Set_5714;
  var snapshot: [int][int]int;
  var i: int;
  var Civl_global_old_state: [int][int]int;
  var Civl_global_old_votes: [int]int;
  var Civl_global_old_B: Set_5714;
  var Civl_global_old_UnallocatedXids: Set_5714;
  var Civl_pc: bool;
  var Civl_ok: bool;
  var Civl_eval: bool;
  var Civl_old_xid: int;
  var Civl_linear_Pair_available: [Pair]bool;

  /*** structured program:
    call xid, pairs := AllocateXid();
    call {:layer 10} snapshot := Copy_7021(state);
    i := 1;
    while (i <= numParticipants)
      invariant Inv_8(state, B, votes);
      invariant pairs == Set_5714((lambda p: Pair :: pair(xid, p->mid, p) && i <= p->mid));
      invariant votes[xid] == -1
         || (forall p: Pair :: 
          Set_Contains_4605(pairs, p) ==> UndecidedOrCommitted(state[xid][p->mid]));
      invariant Inv_9(state, B, xid);
      invariant gConsistent(state);
      invariant ExistsMonotoneExtension(snapshot, state, xid);
      invariant 1 <= i && i <= numParticipants + 1;
    {
        call pair := One_Get(pairs, Pair(xid, i));
        async call {:sync} Participant_VoteReq(xid, i, pair);
        i := i + 1;
    }

    assert {:add_to_pool "A", state[xid]} true;
  **** end structured program */

  Civl_init:
    havoc state, votes, B, UnallocatedXids;
    assume gConsistent(state);
    Civl_global_old_state, Civl_global_old_votes, Civl_global_old_B, Civl_global_old_UnallocatedXids := state, votes, B, UnallocatedXids;
    Civl_pc, Civl_ok, Civl_eval := false, false, false;
    Civl_old_xid := xid;
    assume true;
    Civl_linear_Pair_available := MapOr_5714(Set_Collector_5714(UnallocatedXids), MapConst_5_4577(false));
    goto anon0;

  anon0:
    // <<< injected gate
    assert (forall xid: int :: 
      state[xid] == (lambda j: int :: UNDECIDED())
         ==> 
        Set_IsSubset_4812(perm(xid), UnallocatedXids)
         ==> Set_IsSubset_4812(perm(xid), UnallocatedXids));
    // injected gate >>>
    call xid, pairs := atomic_AllocateXid();
    call {:layer 10} snapshot := Copy_7021(state);
    i := 1;
    goto anon3_LoopHead;

  anon3_LoopHead:
    assume (exists Civl_partition_Pair: [Pair]int :: 
      MapImp_4812(Set_Collector_5714(pairs), MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(0)))
           == MapConst_5_4577(true)
         && MapImp_4812(Set_Collector_5714(UnallocatedXids), 
            MapEq_5714_3(Civl_partition_Pair, MapConst_3_5714(1)))
           == MapConst_5_4577(true));
    assert true;
    assert pairs == Set_5714((lambda p: Pair :: pair(xid, p->mid, p) && i <= p->mid));
    assert true;
    assert true;
    assert gConsistent(state);
    assert ExistsMonotoneExtension(snapshot, state, xid);
    assert 1 <= i && i <= numParticipants + 1;
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    assume {:partition} i <= numParticipants;
    assert Set_Contains_4605(pairs, Pair(xid, i));
    pairs := Set_Remove_4654(pairs, Pair(xid, i));
    pair := One_6657(Pair(xid, i));
    // <<< injected gate
    assert xConsistent(state[xid]);
    assert pair(xid, i, pair->val);
    assert Set_IsDisjoint_4577(perm(xid), UnallocatedXids);
    // injected gate >>>
    call {:sync} atomic_Participant_VoteReq(xid, i, pair);
    i := i + 1;
    goto anon3_LoopHead;

  anon3_LoopDone:
    assume {:partition} numParticipants < i;
    goto anon2;

  anon2:
    assert {:add_to_pool "A", state[xid]} true;
    goto Civl_ReturnChecker, Civl_UnifiedReturn, Civl_NoninterferenceChecker;

  Civl_NoninterferenceChecker:
    call Civl_Wrapper_NoninterferenceChecker_10(Civl_linear_Pair_available, Civl_global_old_state, Civl_global_old_votes, Civl_global_old_B, Civl_global_old_UnallocatedXids);
    assume false;
    return;

  Civl_RefinementChecker:
    assert Civl_pc || state == Civl_global_old_state || Civl_eval;
    assert Civl_pc ==> state == Civl_global_old_state && xid == Civl_old_xid;
    assume false;
    return;

  Civl_UnchangedChecker:
    assert state == Civl_global_old_state;
    assert Civl_pc ==> xid == Civl_old_xid;
    assume false;
    return;

  Civl_ReturnChecker:
    Civl_eval := (exists {:pool "A"} Civl_x#0: [int]int :: 
      xConsistent(state[xid]) && state == Civl_global_old_state[xid := Civl_x#0]);
    assert Civl_pc || state == Civl_global_old_state || Civl_eval;
    assert Civl_pc ==> state == Civl_global_old_state && xid == Civl_old_xid;
    Civl_pc, Civl_ok := state == Civl_global_old_state ==> Civl_pc, Civl_eval || (xid == Civl_old_xid && Civl_ok);
    assert Civl_ok;
    assume false;
    return;

  Civl_UnifiedReturn:
    return;
}



procedure {:inline 1} Civl_NoninterferenceChecker_yield_YieldConsistent_10(Civl_linear_Pair_in: [Pair]bool, 
    Civl_snapshot_state: [int][int]int, 
    Civl_snapshot_votes: [int]int, 
    Civl_snapshot_B: Set_5714, 
    Civl_snapshot_UnallocatedXids: Set_5714);



implementation Civl_NoninterferenceChecker_yield_YieldConsistent_10(Civl_linear_Pair_in: [Pair]bool, 
    Civl_snapshot_state: [int][int]int, 
    Civl_snapshot_votes: [int]int, 
    Civl_snapshot_B: Set_5714, 
    Civl_snapshot_UnallocatedXids: Set_5714)
{

  enter:
    goto exit, L;

  exit:
    return;

  L:
    assume gConsistent(Civl_snapshot_state);
    assert gConsistent(state);
    assume false;
    return;
}



procedure Civl_ParallelCall_Coordinator_TransactionReq_10() returns (Civl_0_xid: int);
  requires gConsistent(state);
  modifies state, votes, B, UnallocatedXids;
  ensures gConsistent(state);



procedure {:inline 1} Civl_Wrapper_NoninterferenceChecker_10(Civl_linear_Pair_in: [Pair]bool, 
    Civl_global_old_state: [int][int]int, 
    Civl_global_old_votes: [int]int, 
    Civl_global_old_B: Set_5714, 
    Civl_global_old_UnallocatedXids: Set_5714);



implementation Civl_Wrapper_NoninterferenceChecker_10(Civl_Civl_linear_Pair_in: [Pair]bool, 
    Civl_Civl_global_old_state: [int][int]int, 
    Civl_Civl_global_old_votes: [int]int, 
    Civl_Civl_global_old_B: Set_5714, 
    Civl_Civl_global_old_UnallocatedXids: Set_5714)
{

  enter:
    goto L_0;

  L_0:
    call Civl_NoninterferenceChecker_yield_YieldConsistent_10(Civl_Civl_linear_Pair_in, Civl_Civl_global_old_state, Civl_Civl_global_old_votes, Civl_Civl_global_old_B, Civl_Civl_global_old_UnallocatedXids);
    return;
}



procedure Civl_main_11();
  modifies state, votes, B, UnallocatedXids;



implementation Civl_main_11()
{
  var xid: int;
  var Civl_global_old_state: [int][int]int;
  var Civl_global_old_votes: [int]int;
  var Civl_global_old_B: Set_5714;
  var Civl_global_old_UnallocatedXids: Set_5714;
  var Civl_pc: bool;
  var Civl_ok: bool;
  var Civl_eval: bool;
  var Civl_linear_Pair_available: [Pair]bool;

  /*** structured program:
    while (*)
      invariant      call YieldInv_8();
      invariant      call YieldConsistent_9();
      invariant      call YieldConsistent_10();
      invariant {:yields} true;
    {
        call xid := Coordinator_TransactionReq();
    }
  **** end structured program */

  Civl_init:
    havoc state, votes, B, UnallocatedXids;
    Civl_global_old_state, Civl_global_old_votes, Civl_global_old_B, Civl_global_old_UnallocatedXids := state, votes, B, UnallocatedXids;
    Civl_pc, Civl_ok, Civl_eval := false, false, false;
    assume true;
    Civl_linear_Pair_available := MapConst_5_4577(false);
    goto anon0;

  anon0:
    goto anon2_LoopHead, Civl_NoninterferenceChecker, Civl_RefinementChecker;

  anon2_LoopHead:
    assume Civl_pc || true;
    state, votes, B, UnallocatedXids := state, votes, B, UnallocatedXids;
    Civl_global_old_state, Civl_global_old_votes, Civl_global_old_B, Civl_global_old_UnallocatedXids := state, votes, B, UnallocatedXids;
    Civl_linear_Pair_available := MapConst_5_4577(false);
    goto anon2_LoopDone, anon2_LoopBody;

  anon2_LoopBody:
    call xid := atomic_Coordinator_TransactionReq();
    goto anon2_LoopHead, Civl_NoninterferenceChecker, Civl_UnchangedChecker;

  anon2_LoopDone:
    goto Civl_ReturnChecker, Civl_UnifiedReturn, Civl_NoninterferenceChecker;

  Civl_NoninterferenceChecker:
    call Civl_Wrapper_NoninterferenceChecker_11(Civl_linear_Pair_available, Civl_global_old_state, Civl_global_old_votes, Civl_global_old_B, Civl_global_old_UnallocatedXids);
    assume false;
    return;

  Civl_RefinementChecker:
    assert true;
    assert Civl_pc ==> true;
    assume false;
    return;

  Civl_UnchangedChecker:
    assert true;
    assert Civl_pc ==> true;
    assume false;
    return;

  Civl_ReturnChecker:
    Civl_eval := true;
    assert true;
    assert Civl_pc ==> true;
    Civl_pc, Civl_ok := true ==> Civl_pc, Civl_eval || Civl_ok;
    assert Civl_ok;
    assume false;
    return;

  Civl_UnifiedReturn:
    return;
}



procedure {:inline 1} Civl_Wrapper_NoninterferenceChecker_11(Civl_linear_Pair_in: [Pair]bool, 
    Civl_global_old_state: [int][int]int, 
    Civl_global_old_votes: [int]int, 
    Civl_global_old_B: Set_5714, 
    Civl_global_old_UnallocatedXids: Set_5714);



implementation Civl_Wrapper_NoninterferenceChecker_11(Civl_Civl_linear_Pair_in: [Pair]bool, 
    Civl_Civl_global_old_state: [int][int]int, 
    Civl_Civl_global_old_votes: [int]int, 
    Civl_Civl_global_old_B: Set_5714, 
    Civl_Civl_global_old_UnallocatedXids: Set_5714)
{

  enter:
    return;
}


