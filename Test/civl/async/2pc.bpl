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

type {:datatype} {:linear "pair"} Pair;
function {:constructor} Pair (xid: Xid, mid: Mid) : Pair;

function {:inline} pair (xid: Xid, mid: Mid, p: Pair) : bool
{ p == Pair(xid, mid) && participantMid(p->mid) }

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

var {:linear "pair"} {:layer 7,9} B : [Pair]bool;
var {:layer 7,10}{:linear "pair"} UnallocatedXids: [Xid]bool;

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

function {:inline} xAllParticipantsInB (xid: Xid, B: [Pair]bool) : bool
{
  (forall mid: Mid :: participantMid(mid) ==> B[Pair(xid, mid)])
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

function {:inline} Inv_8 (state: GState, B: [Pair]bool, votes: [Xid]int) : bool
{
     gConsistent(state)
  && SetInv(B)
  && (forall xid: Xid :: VotesEqCoordinatorState(votes, state, xid))
  && (forall xid: Xid :: votes[xid] == -1 || votes[xid] == card(B, xid))
  && (forall p: Pair :: B[p] && votes[p->xid] != -1 ==> UndecidedOrCommitted(state[p->xid][p->mid]))
}

function {:inline} Inv_9 (state: GState, B: [Pair]bool, xid: Xid) : bool
{
     gConsistent(state)
  && (xAllParticipantsInB(xid, B) || xUndecidedOrAborted(state[xid]))
}

procedure {:yield_invariant} {:layer 8} YieldInv_8 ();
requires Inv_8(state, B, votes);

procedure {:yield_invariant} {:layer 8} YieldUndecidedOrCommitted_8 (xid: Xid, mid: Mid, {:linear "pair"} pair: Pair);
requires pair(xid, mid, pair) && (votes[xid] == -1 || UndecidedOrCommitted(state[xid][mid]));

procedure {:yield_invariant} {:layer 8} YieldAborted_8 (xid: Xid, mid: Mid, {:linear "pair"} pair: Pair);
requires pair(xid, mid, pair) && Aborted(state[xid][mid]);

procedure {:yield_invariant} {:layer 9} YieldInv_9 (xid: Xid);
requires Inv_9(state, B, xid);

procedure {:yield_invariant} {:layer 9} YieldConsistent_9 ();
requires gConsistent(state);

procedure {:yield_invariant} {:layer 10} YieldConsistent_10 ();
requires gConsistent(state);

// ###########################################################################
// Main

procedure {:yields} {:layer 11}
{:yield_requires "YieldInv_8"}
{:yield_requires "YieldConsistent_9"}
{:yield_requires "YieldConsistent_10"}
main ()
{
  var xid: Xid;
  while (*)
  invariant {:yields}{:layer 8,9,10,11}
    {:yield_loop "YieldInv_8"}
    {:yield_loop "YieldConsistent_9"}
    {:yield_loop "YieldConsistent_10"}
    true;
  {
    call xid := Coordinator_TransactionReq();
  }
}

// ###########################################################################
// Event Handlers

procedure {:intro} {:layer 8} GhostRead_8() returns (snapshot: GState)
{
   snapshot := state;
}

procedure {:intro} {:layer 10} GhostRead_10() returns (snapshot: GState)
{
   snapshot := state;
}

procedure {:atomic} {:layer 11} atomic_Coordinator_TransactionReq () returns (xid: Xid)
modifies state;
{
  var {:pool "A"} x: XState;
  state[xid] := x;
  assume xConsistent(state[xid]);
}

procedure {:yields} {:layer 10} {:refines "atomic_Coordinator_TransactionReq"}
{:yield_preserves "YieldInv_8"}
{:yield_preserves "YieldConsistent_9"}
{:yield_preserves "YieldConsistent_10"}
Coordinator_TransactionReq () returns (xid: Xid)
{
  var {:linear "pair"} pair: Pair;
  var {:linear "pair"} pairs: [Pair]bool;
  var {:layer 10} snapshot: GState;
  var i : Mid;

  call xid, pairs := AllocateXid();
  call snapshot := GhostRead_10();
  i := 1;
  while (i <= numParticipants)
  invariant {:cooperates} {:layer 8,9,10} true;
  invariant {:layer 8} Inv_8(state, B, votes);
  invariant {:layer 8,10} pairs == (lambda p: Pair :: pair(xid, p->mid, p) && i <= p->mid);
  invariant {:layer 8} votes[xid] == -1 || (forall p: Pair :: pairs[p] ==> UndecidedOrCommitted(state[xid][p->mid]));
  invariant {:layer 9} Inv_9(state, B, xid);
  invariant {:layer 10} gConsistent(state);
  invariant {:layer 10} ExistsMonotoneExtension(snapshot, state, xid);
  invariant {:layer 10} 1 <= i && i <= numParticipants + 1;
  {
    call pairs, pair := TransferPair(xid, i, pairs);
    async call {:sync} Participant_VoteReq(xid, i, pair);
    i := i + 1;
  }

  assert {:layer 10} {:add_to_pool "A", state[xid]} true;
}

// ---------------------------------------------------------------------------

procedure {:left} {:layer 10} atomic_Participant_VoteReq (xid: Xid, mid: Mid, {:linear_in "pair"} pair: Pair)
modifies state;
{
  var {:pool "A"} x: XState;
  assert !UnallocatedXids[xid];
  assert pair(xid, mid, pair);
  assert xConsistent(state[xid]);
  state[xid] := x;
  assume xConsistentExtension(old(state)[xid], state[xid]);
}

procedure {:yields} {:layer 9} {:refines "atomic_Participant_VoteReq"}
{:yield_requires "YieldInv_8"}
{:yield_requires "YieldUndecidedOrCommitted_8", xid, mid, pair}
{:yield_requires "YieldInv_9", xid}
Participant_VoteReq (xid: Xid, mid: Mid, {:linear_in "pair"} pair: Pair)
{
  if (*) {
    async call {:sync} Coordinator_VoteYes(xid, mid, pair);
  } else {
    call SetParticipantAborted(xid, mid, pair);
    async call {:sync} Coordinator_VoteNo(xid, mid, pair);
  }

  assert {:layer 9} {:add_to_pool "A", state[xid]} true;
}

// ---------------------------------------------------------------------------

procedure {:left} {:layer 9} atomic_Coordinator_VoteYes (xid: Xid, mid: Mid, {:linear_in "pair"} pair: Pair)
modifies state, B;
{
  var {:pool "A"} x: XState;
  assert !UnallocatedXids[xid];
  assert pair(xid, mid, pair);
  assert xConsistent(state[xid]);
  B[pair] := true;
  if (*) {
    state[xid] := x;
    assume xAllParticipantsInB(xid, B);
    assume xConsistentExtension(old(state)[xid], state[xid]);
  }
}

procedure {:yields} {:layer 8} {:refines "atomic_Coordinator_VoteYes"}
{:yield_requires "YieldInv_8"}
{:yield_requires "YieldUndecidedOrCommitted_8", xid, mid, pair}
Coordinator_VoteYes (xid: Xid, mid: Mid, {:linear_in "pair"} pair: Pair)
{
  var commit : bool;
  var i : Mid;
  var {:layer 8} snapshot: GState;

  call snapshot := GhostRead_8();
  call {:layer 8} Lemma_add_to_set(B, pair);
  call {:layer 8} Lemma_all_in_set(B, xid);
  call commit := StateUpdateOnVoteYes(xid, mid, pair);
  call {:layer 8} Lemma_all_in_set(B, xid);

  if (commit)
  {
    assert {:layer 8} xUndecidedOrCommitted(snapshot[xid]);
    assert {:layer 8} xUndecidedOrCommitted(state[xid]);
    i := 1;
    while (i <= numParticipants)
    invariant {:layer 8} {:cooperates} true;
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

procedure {:left} {:layer 9} atomic_Coordinator_VoteNo (xid: Xid, mid: Mid, {:linear_in "pair"} pair: Pair)
modifies state;
{
  var {:pool "A"} x: XState;
  assert !UnallocatedXids[xid];
  assert pair(xid, mid, pair);
  assert xUndecidedOrAborted(state[xid]);
  state[xid] := x;
  assume xUndecidedOrAborted(state[xid]);
  assume xConsistentExtension(old(state)[xid], state[xid]);
}

procedure {:yields} {:layer 8} {:refines "atomic_Coordinator_VoteNo"}
{:yield_requires "YieldAborted_8", xid, mid, pair}
Coordinator_VoteNo (xid: Xid, mid: Mid, {:linear_in "pair"} pair: Pair)
{
  var abort : bool;
  var i : int;
  var {:layer 8} snapshot: GState;

  call snapshot := GhostRead_8();
  call abort := StateUpdateOnVoteNo(xid, mid);

  if (abort)
  {
    i := 1;
    while (i <= numParticipants)
    invariant {:layer 8} {:cooperates} true;
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

procedure {:yields} {:layer 7} {:refines "atomic_SetParticipantAborted"} SetParticipantAborted (xid: Xid, mid: Mid, {:linear "pair"} pair: Pair);
procedure {:yields} {:layer 7} {:refines "atomic_StateUpdateOnVoteYes"} StateUpdateOnVoteYes (xid: Xid, mid: Mid, {:linear_in "pair"} pair: Pair) returns (commit : bool);
procedure {:yields} {:layer 7} {:refines "atomic_StateUpdateOnVoteNo"} StateUpdateOnVoteNo (xid: Xid, mid: Mid) returns (abort : bool);
procedure {:yields} {:layer 7} {:refines "atomic_Participant_Commit"} Participant_Commit (xid : Xid, mid : Mid);
procedure {:yields} {:layer 7} {:refines "atomic_Participant_Abort"} Participant_Abort (xid : Xid, mid : Mid);

procedure {:atomic} {:layer 8,9} atomic_SetParticipantAborted (xid: Xid, mid: Mid, {:linear "pair"} pair: Pair)
modifies state;
{
  assert pair(xid, mid, pair);
  assert xUndecidedOrAborted(state[xid]);
  state[xid][mid] := ABORTED();
}

procedure {:atomic} {:layer 8} atomic_StateUpdateOnVoteYes (xid: Xid, mid: Mid, {:linear_in "pair"} pair: Pair) returns (commit : bool)
modifies votes, state, B;
{
  assert !UnallocatedXids[xid];
  assert VotesEqCoordinatorState(votes, state, xid);
  B[pair] := true;
  if (votes[xid] == -1) {
    commit := false;
  } else {
    votes[xid] := votes[xid] + 1;
    commit := (votes[xid] == numParticipants);
    state[xid][CoordinatorMid] := (if commit then COMMITTED() else state[xid][CoordinatorMid]);
  }
}

procedure {:atomic} {:layer 8} atomic_StateUpdateOnVoteNo (xid: Xid, mid: Mid) returns (abort : bool)
modifies votes, state;
{
  assert !UnallocatedXids[xid];
  assert !Committed(state[xid][CoordinatorMid]);
  abort := (votes[xid] != -1);
  votes[xid] := -1;
  state[xid][CoordinatorMid] := (if abort then ABORTED() else state[xid][CoordinatorMid]);
}

// ---------------------------------------------------------------------------

procedure {:left} {:layer 8} atomic_Participant_Commit (xid : Xid, mid : Mid)
modifies state;
{
  assert participantMid(mid);
  assert xUndecidedOrCommitted(state[xid]);
  assert Committed(state[xid][CoordinatorMid]);
  state[xid][mid] := COMMITTED();
}

procedure {:left} {:layer 8} atomic_Participant_Abort (xid : Xid, mid : Mid)
modifies state;
{
  assert participantMid(mid);
  assert xUndecidedOrAborted(state[xid]);
  assert Aborted(state[xid][CoordinatorMid]);
  state[xid][mid] := ABORTED();
}

// ###########################################################################
// Linear variable allocation

procedure {:yields} {:layer 7} {:refines "atomic_AllocateXid"} AllocateXid () returns (xid: Xid, {:linear "pair"} pairs: [Pair]bool);
procedure {:yields} {:layer 7} {:refines "atomic_TransferPair"} TransferPair (xid: Xid, mid: Mid, {:linear_in "pair"} inPairs: [Pair]bool) returns ({:linear "pair"} pairs: [Pair]bool, {:linear "pair"} pair: Pair);

procedure {:atomic} {:layer 8,10} atomic_AllocateXid () returns (xid: Xid, {:linear "pair"} pairs: [Pair]bool)
modifies UnallocatedXids;
{
  assume UnallocatedXids[xid];
  assume state[xid] == (lambda j: Mid :: UNDECIDED());
  pairs := (lambda p: Pair :: pair(xid, p->mid, p));
  UnallocatedXids[xid] := false;
}

procedure {:both} {:layer 8,10} atomic_TransferPair (xid: Xid, mid: Mid, {:linear_in "pair"} inPairs: [Pair]bool) returns ({:linear "pair"} pairs: [Pair]bool, {:linear "pair"} pair: Pair)
{
  assert inPairs[Pair(xid, mid)];
  pair := Pair(xid, mid);
  pairs := inPairs[pair := false];
}

// ###########################################################################
// Collectors for linear domains

function {:inline} {:linear "pair"} XidSetCollector(xids: [Xid]bool) : [Pair]bool
{
  (lambda p: Pair :: xids[p->xid])
}

// ############################################################################
// Lemmas about cardinality

function card(pairs: [Pair]bool, xid: Xid) : int;

procedure {:lemma} Lemma_add_to_set (set: [Pair]bool, pair: Pair);
requires participantMid(pair->mid);
requires !set[pair];
ensures (forall xid: Xid :: card(set[pair := true], xid) == (if xid == pair->xid then card(set, xid) + 1 else card(set, xid)));

procedure {:lemma} Lemma_all_in_set (set: [Pair]bool, xid: Xid);
requires SetInv(set);
ensures card(set, xid) >= numParticipants ==> (forall mid: Mid :: participantMid(mid) ==> set[Pair(xid, mid)]);
