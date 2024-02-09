// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ###########################################################################
// Type declarations

// Transaction and Machine IDs
type Xid = int;
type Mid = int;

const CoordinatorMid : Mid;
axiom CoordinatorMid == 0;
function coordinatorMid (mid : Mid) : bool { mid == CoordinatorMid }

const numParticipants : int;
axiom 0 < numParticipants;
function participantMid (mid : Mid) : bool { 1 <= mid && mid <= numParticipants }

datatype Pair { Pair(xid: Xid, mid: Mid) }

function {:inline} pair (xid: Xid, mid: Mid, p: Pair) : bool
{ p == Pair(xid, mid) && participantMid(p->mid) }

function {:inline} perm (xid: Xid) : Set Pair
{ Set((lambda p: Pair :: pair(xid, p->mid, p))) }

// Transaction State
type MState = int;
function {:inline} ABORTED   () : int { 0 }
function {:inline} UNDECIDED () : int { 1 }
function {:inline} COMMITTED () : int { 2 }
function {:inline} Aborted   (i:MState) : bool { i == ABORTED() }
function {:inline} Undecided (i:MState) : bool { i == UNDECIDED() }
function {:inline} Committed (i:MState) : bool { i == COMMITTED() }
function {:inline} UndecidedOrAborted   (i:MState) : bool { Undecided(i) || Aborted(i) }
function {:inline} UndecidedOrCommitted (i:MState) : bool { Undecided(i) || Committed(i) }

type XState = [Mid]MState;
type GState = [Xid]XState;

// ###########################################################################
// Global shared variables

var {:layer 0,11} state : GState;
var {:layer 7,8} votes : [Xid]int;

var {:linear} {:layer 7,9} B: Set Pair;
var {:linear} {:layer 7,10} UnallocatedXids: Set Pair;

// ###########################################################################
// Consistency Predicates

// Transaction (indicated by prefix x)

function {:inline} xUndecided (state: XState) : bool
{
  Undecided(state[CoordinatorMid]) &&
  (forall i : Mid :: participantMid(i) ==> Undecided(state[i]))
}

function {:inline} xUndecidedOrCommitted (state: XState) : bool
{
  UndecidedOrCommitted(state[CoordinatorMid]) &&
  (forall i : Mid :: participantMid(i) ==> UndecidedOrCommitted(state[i]))
}

function {:inline} xUndecidedOrAborted (state: XState) : bool
{
  UndecidedOrAborted(state[CoordinatorMid]) &&
  (forall i : Mid :: participantMid(i) ==> UndecidedOrAborted(state[i]))
}

function {:inline} xConsistent (state: XState) : bool
{
  xUndecidedOrCommitted(state) || xUndecidedOrAborted(state)
}

function {:inline} xNoUndoneDecision (oldState: XState, newState: XState) : bool
{
  (newState[CoordinatorMid] == oldState[CoordinatorMid] || Undecided(oldState[CoordinatorMid])) &&
  (forall i : Mid :: participantMid(i) ==> (newState[i] == oldState[i] || Undecided(oldState[i])))
}

function {:inline} xConsistentExtension (oldState: XState, newState: XState) : bool
{
  xConsistent(newState) &&
  xNoUndoneDecision(oldState, newState)
}

function {:inline} xAllParticipantsInB (xid: Xid, B: Set Pair) : bool
{
  (forall mid: Mid :: participantMid(mid) ==> Set_Contains(B, Pair(xid, mid)))
}

// Globally across transactions (indicated by prefix g)

function {:inline} gUndecided (state: GState) : bool
{
  (forall j: Xid :: xUndecided(state[j]))
}

function {:inline} gConsistent (state: GState) : bool
{
  (forall j: Xid :: xConsistent(state[j]))
}

// Helper predicates

function {:inline} ExistsMonotoneExtension (snapshot: GState, state: GState, xid: Xid) : bool
{
  (exists newState: XState ::
    state == snapshot[xid := newState] && xNoUndoneDecision(snapshot[xid],newState))
}

function {:inline} VotesEqCoordinatorState (votes: [Xid]int, state: GState, xid: Xid) : bool
{
     ( (votes[xid] == -1)                                == Aborted  (state[xid][CoordinatorMid]) )
  && ( (0 <= votes[xid] && votes[xid] < numParticipants) == Undecided(state[xid][CoordinatorMid]) )
  && ( (votes[xid] == numParticipants)                   == Committed(state[xid][CoordinatorMid]) )
}

// ###########################################################################
// Yield assertions

function {:inline} SetInv (B: [Pair]bool) : bool
{
  (forall xid: Xid, mid: Mid :: B[Pair(xid,mid)] ==> participantMid(mid))
}

function {:inline} Inv_8 (state: GState, B: Set Pair, votes: [Xid]int) : bool
{
     gConsistent(state)
  && SetInv(B->val)
  && (forall xid: Xid :: VotesEqCoordinatorState(votes, state, xid))
  && (forall xid: Xid :: votes[xid] == -1 || votes[xid] == card(B->val, xid))
  && (forall p: Pair :: Set_Contains(B, p) && votes[p->xid] != -1 ==> UndecidedOrCommitted(state[p->xid][p->mid]))
}

function {:inline} Inv_9 (state: GState, B: Set Pair, xid: Xid) : bool
{
     gConsistent(state)
  && (xAllParticipantsInB(xid, B) || xUndecidedOrAborted(state[xid]))
}

yield invariant {:layer 8} YieldInv_8 ();
invariant Inv_8(state, B, votes);

yield invariant {:layer 8} YieldUndecidedOrCommitted_8 (xid: Xid, mid: Mid, {:linear} pair: One Pair);
invariant pair(xid, mid, pair->val) && (votes[xid] == -1 || UndecidedOrCommitted(state[xid][mid]));

yield invariant {:layer 8} YieldAborted_8 (xid: Xid, mid: Mid, {:linear} pair: One Pair);
invariant pair(xid, mid, pair->val) && Aborted(state[xid][mid]);

yield invariant {:layer 9} YieldInv_9 (xid: Xid);
invariant Inv_9(state, B, xid);

yield invariant {:layer 9} YieldConsistent_9 ();
invariant gConsistent(state);

yield invariant {:layer 10} YieldConsistent_10 ();
invariant gConsistent(state);

// ###########################################################################
// Main

yield procedure {:layer 11}
main ()
requires call YieldInv_8();
requires call YieldConsistent_9();
requires call YieldConsistent_10();
{
  var xid: Xid;
  while (*)
  invariant {:yields} true;
  invariant call YieldInv_8();
  invariant call YieldConsistent_9();
  invariant call YieldConsistent_10();
  {
    call xid := Coordinator_TransactionReq();
  }
}

// ###########################################################################
// Event Handlers

atomic action {:layer 11} atomic_Coordinator_TransactionReq () returns (xid: Xid)
modifies state;
{
  var {:pool "A"} x: XState;
  state[xid] := x;
  assume xConsistent(state[xid]);
}

yield procedure {:layer 10}
Coordinator_TransactionReq () returns (xid: Xid)
refines atomic_Coordinator_TransactionReq;
preserves call YieldInv_8();
preserves call YieldConsistent_9();
preserves call YieldConsistent_10();
{
  var {:linear} pair: One Pair;
  var {:linear} pairs: Set Pair;
  var {:layer 10} snapshot: GState;
  var i : Mid;

  call xid, pairs := AllocateXid();
  call {:layer 10} snapshot := Copy(state);
  i := 1;
  while (i <= numParticipants)
  invariant {:layer 8} Inv_8(state, B, votes);
  invariant {:layer 8,9,10} pairs == Set((lambda p: Pair :: pair(xid, p->mid, p) && i <= p->mid));
  invariant {:layer 8} votes[xid] == -1 || (forall p: Pair :: Set_Contains(pairs, p) ==> UndecidedOrCommitted(state[xid][p->mid]));
  invariant {:layer 9} Inv_9(state, B, xid);
  invariant {:layer 10} gConsistent(state);
  invariant {:layer 10} ExistsMonotoneExtension(snapshot, state, xid);
  invariant {:layer 8,9,10} 1 <= i && i <= numParticipants + 1;
  {
    call pair := One_Get(pairs, Pair(xid, i));
    async call {:sync} Participant_VoteReq(xid, i, pair);
    i := i + 1;
  }

  assert {:layer 10} {:add_to_pool "A", state[xid]} true;
}

// ---------------------------------------------------------------------------

left action {:layer 10} atomic_Participant_VoteReq (xid: Xid, mid: Mid, {:linear_in} pair: One Pair)
modifies state;
{
  var {:pool "A"} x: XState;
  assert Set_IsDisjoint(perm(xid), UnallocatedXids);
  assert pair(xid, mid, pair->val);
  assert xConsistent(state[xid]);
  state[xid] := x;
  assume xConsistentExtension(old(state)[xid], state[xid]);
}

yield procedure {:layer 9}
Participant_VoteReq (xid: Xid, mid: Mid, {:linear_in} pair: One Pair)
refines atomic_Participant_VoteReq;
requires call YieldInv_8();
requires call YieldUndecidedOrCommitted_8(xid, mid, pair);
requires call YieldInv_9(xid);
{
  if (*) {
    async call {:sync} Coordinator_VoteYes(xid, mid, pair);
  } else {
    call SetParticipantAborted(xid, mid, pair);
    async call {:sync} Coordinator_VoteNo(xid, mid, pair);
  }

  assume {:add_to_pool "A", state[xid]} true;
}

// ---------------------------------------------------------------------------

left action {:layer 9} atomic_Coordinator_VoteYes (xid: Xid, mid: Mid, {:linear_in} pair: One Pair)
modifies state, B;
{
  var {:pool "A"} x: XState;
  assert Set_IsDisjoint(perm(xid), UnallocatedXids);
  assert pair(xid, mid, pair->val);
  assert xConsistent(state[xid]);
  call One_Put(B, pair);
  if (*) {
    state[xid] := x;
    assume xAllParticipantsInB(xid, B);
    assume xConsistentExtension(old(state)[xid], state[xid]);
  }
}

yield procedure {:layer 8}
Coordinator_VoteYes (xid: Xid, mid: Mid, {:linear_in} pair: One Pair)
refines atomic_Coordinator_VoteYes;
requires call YieldInv_8();
requires call YieldUndecidedOrCommitted_8(xid, mid, pair);
{
  var commit : bool;
  var i : Mid;
  var {:layer 8} snapshot: GState;

  call {:layer 8} snapshot := Copy(state);
  call {:layer 8} Lemma_add_to_set(B->val, pair->val);
  call {:layer 8} Lemma_all_in_set(B->val, xid);
  call commit := StateUpdateOnVoteYes(xid, mid, pair);
  call {:layer 8} Lemma_all_in_set(B->val, xid);

  if (commit)
  {
    assert {:layer 8} xUndecidedOrCommitted(snapshot[xid]);
    assert {:layer 8} xUndecidedOrCommitted(state[xid]);
    i := 1;
    while (i <= numParticipants)
    invariant {:layer 8} 1 <= i && i <= numParticipants + 1;
    invariant {:layer 8} Inv_8(state, B, votes);
    invariant {:layer 8} ExistsMonotoneExtension(snapshot, state, xid);
    {
      async call {:sync} Participant_Commit(xid, i);
      i := i + 1;
    }
  }

  assert {:layer 8} {:add_to_pool "A", state[xid]} true;
}

left action {:layer 9} atomic_Coordinator_VoteNo (xid: Xid, mid: Mid, {:linear_in} pair: One Pair)
modifies state;
{
  var {:pool "A"} x: XState;
  assert Set_IsDisjoint(perm(xid), UnallocatedXids);
  assert pair(xid, mid, pair->val);
  assert xUndecidedOrAborted(state[xid]);
  state[xid] := x;
  assume xUndecidedOrAborted(state[xid]);
  assume xConsistentExtension(old(state)[xid], state[xid]);
}

yield procedure {:layer 8}
Coordinator_VoteNo (xid: Xid, mid: Mid, {:linear_in} pair: One Pair)
refines atomic_Coordinator_VoteNo;
requires call YieldAborted_8(xid, mid, pair);
{
  var abort : bool;
  var i : int;
  var {:layer 8} snapshot: GState;

  call {:layer 8} snapshot := Copy(state);
  call abort := StateUpdateOnVoteNo(xid, mid);

  if (abort)
  {
    i := 1;
    while (i <= numParticipants)
    invariant {:layer 8} 1 <= i && i <= numParticipants + 1;
    invariant {:layer 8} Aborted(state[xid][CoordinatorMid]);
    invariant {:layer 8} xUndecidedOrAborted(state[xid]);
    invariant {:layer 8} ExistsMonotoneExtension(snapshot, state, xid);
    {
      async call {:sync} Participant_Abort(xid, i);
      i := i + 1;
    }
  }

  assert {:layer 8} {:add_to_pool "A", state[xid]} true;
}

// ---------------------------------------------------------------------------

yield procedure {:layer 7} SetParticipantAborted (xid: Xid, mid: Mid, {:linear} pair: One Pair);
refines atomic_SetParticipantAborted;

yield procedure {:layer 7} StateUpdateOnVoteYes (xid: Xid, mid: Mid, {:linear_in} pair: One Pair) returns (commit : bool);
refines atomic_StateUpdateOnVoteYes;

yield procedure {:layer 7} StateUpdateOnVoteNo (xid: Xid, mid: Mid) returns (abort : bool);
refines atomic_StateUpdateOnVoteNo;

yield procedure {:layer 7} Participant_Commit (xid : Xid, mid : Mid);
refines atomic_Participant_Commit;

yield procedure {:layer 7} Participant_Abort (xid : Xid, mid : Mid);
refines atomic_Participant_Abort;

atomic action {:layer 8,9} atomic_SetParticipantAborted (xid: Xid, mid: Mid, {:linear} pair: One Pair)
modifies state;
{
  assert pair(xid, mid, pair->val);
  assert xUndecidedOrAborted(state[xid]);
  state[xid][mid] := ABORTED();
}

atomic action {:layer 8} atomic_StateUpdateOnVoteYes (xid: Xid, mid: Mid, {:linear_in} pair: One Pair) returns (commit : bool)
modifies votes, state, B;
{
  assert Set_IsDisjoint(perm(xid), UnallocatedXids);
  assert VotesEqCoordinatorState(votes, state, xid);
  call One_Put(B, pair);
  if (votes[xid] == -1) {
    commit := false;
  } else {
    votes[xid] := votes[xid] + 1;
    commit := (votes[xid] == numParticipants);
    state[xid][CoordinatorMid] := (if commit then COMMITTED() else state[xid][CoordinatorMid]);
  }
}

atomic action {:layer 8} atomic_StateUpdateOnVoteNo (xid: Xid, mid: Mid) returns (abort : bool)
modifies votes, state;
{
  assert Set_IsDisjoint(perm(xid), UnallocatedXids);
  assert !Committed(state[xid][CoordinatorMid]);
  abort := (votes[xid] != -1);
  votes[xid] := -1;
  state[xid][CoordinatorMid] := (if abort then ABORTED() else state[xid][CoordinatorMid]);
}

// ---------------------------------------------------------------------------

left action {:layer 8} atomic_Participant_Commit (xid : Xid, mid : Mid)
modifies state;
{
  assert participantMid(mid);
  assert xUndecidedOrCommitted(state[xid]);
  assert Committed(state[xid][CoordinatorMid]);
  state[xid][mid] := COMMITTED();
}

left action {:layer 8} atomic_Participant_Abort (xid : Xid, mid : Mid)
modifies state;
{
  assert participantMid(mid);
  assert xUndecidedOrAborted(state[xid]);
  assert Aborted(state[xid][CoordinatorMid]);
  state[xid][mid] := ABORTED();
}

// ###########################################################################
// Linear variable allocation

atomic action {:layer 8,10} atomic_AllocateXid () returns (xid: Xid, {:linear} pairs: Set Pair)
modifies UnallocatedXids;
{
  assume state[xid] == (lambda j: Mid :: UNDECIDED());
  pairs := perm(xid);
  assume Set_IsSubset(pairs, UnallocatedXids);
  call Set_Split(UnallocatedXids, pairs);
}
yield procedure {:layer 7} AllocateXid () returns (xid: Xid, {:linear} pairs: Set Pair);
refines atomic_AllocateXid;

// ############################################################################
// Lemmas about cardinality

function card(pairs: [Pair]bool, xid: Xid) : int;

pure procedure Lemma_add_to_set (set: [Pair]bool, pair: Pair);
requires participantMid(pair->mid);
requires !set[pair];
ensures (forall xid: Xid :: card(set[pair := true], xid) == (if xid == pair->xid then card(set, xid) + 1 else card(set, xid)));

pure procedure Lemma_all_in_set (set: [Pair]bool, xid: Xid);
requires SetInv(set);
ensures card(set, xid) >= numParticipants ==> (forall mid: Mid :: participantMid(mid) ==> set[Pair(xid, mid)]);
