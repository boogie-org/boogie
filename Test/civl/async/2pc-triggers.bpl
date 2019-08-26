// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
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

type {:datatype} Pair;
function {:constructor} Pair (xid: Xid, mid: Mid) : Pair;

function {:inline} pair (xid: Xid, mid: Mid, p: Pair) : bool
{ p == Pair(xid, mid) && participantMid(mid#Pair(p)) }

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
  (forall i : Mid :: {participantMid(i)} participantMid(i) ==> (newState[i] == oldState[i] || Undecided(oldState[i])))
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

function NextStateTrigger (XState): bool
{
    true
}

function XidTrigger (xid: Xid): bool
{
    true
}

function {:inline} ExistsMonotoneExtension (snapshot: GState, state: GState, xid: Xid) : bool
{
  (exists newState: XState :: {NextStateTrigger(newState)}
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

procedure {:yield_assert} {:layer 8} YieldInv_8 ()
       requires {:layer 8} Inv_8(state, B, votes);
{ yield; assert {:layer 8} Inv_8(state, B, votes); }

procedure {:yield_assert} {:layer 8} YieldPairs_8 (xid: Xid, {:linear "pair"} pairs: [Pair]bool)
       requires {:layer 8} Inv_8(state, B, votes) && (votes[xid] == -1 || (forall p: Pair :: pairs[p] ==> pair(xid, mid#Pair(p), p) && UndecidedOrCommitted(state[xid][mid#Pair(p)])));
{ yield; assert {:layer 8} Inv_8(state, B, votes) && (votes[xid] == -1 || (forall p: Pair :: pairs[p] ==> pair(xid, mid#Pair(p), p) && UndecidedOrCommitted(state[xid][mid#Pair(p)]))); }

procedure {:yield_assert} {:layer 8} YieldUndecidedOrCommitted_8 (xid: Xid, mid: Mid, {:linear "pair"} pair: Pair)
       requires {:layer 8} Inv_8(state, B, votes) && pair(xid, mid, pair) && (votes[xid] == -1 || UndecidedOrCommitted(state[xid][mid]));
{ yield; assert {:layer 8} Inv_8(state, B, votes) && pair(xid, mid, pair) && (votes[xid] == -1 || UndecidedOrCommitted(state[xid][mid])); }

procedure {:yield_assert} {:layer 8} YieldAborted_8 (xid: Xid, mid: Mid, {:linear "pair"} pair: Pair)
       requires {:layer 8} Inv_8(state, B, votes) && pair(xid, mid, pair) && Aborted(state[xid][mid]);
{ yield; assert {:layer 8} Inv_8(state, B, votes) && pair(xid, mid, pair) && Aborted(state[xid][mid]); }

procedure {:yield_assert} {:layer 9} YieldInv_9 (xid: Xid)
       requires {:layer 9} Inv_9(state, B, xid);
{ yield; assert {:layer 9} Inv_9(state, B, xid); }

procedure {:yield_assert} {:layer 9} YieldConsistent_9 ()
       requires {:layer 9} gConsistent(state);
{ yield; assert {:layer 9} gConsistent(state); }

procedure {:yield_assert} {:layer 10} YieldConsistent_10 ()
       requires {:layer 10} gConsistent(state);
{ yield; assert {:layer 10} gConsistent(state); }

procedure {:yield_assert} {:layer 11} YieldConsistent_11 ()
       requires {:layer 11} gConsistent(state);
{ yield; assert {:layer 11} gConsistent(state); }

// ###########################################################################
// Main

procedure {:yields} {:layer 11} main ()
// requires {:layer 8} Inv_8(state, B, votes);
requires {:layer 8,9,10,11} gUndecided(state);
requires {:layer 8} votes == (lambda xid: Xid :: 0);
requires {:layer 8} B == (lambda p: Pair :: false);
requires {:layer 8} (forall B: [Pair]bool, xid: Xid :: card(B, xid) == 0);
{
  var xid: Xid;
  par YieldInv_8() | YieldConsistent_9() | YieldConsistent_10() | YieldConsistent_11();
  while (*)
  invariant {:layer 8} Inv_8(state, B, votes);
  invariant {:layer 9,10,11} gConsistent(state);
  {
    call xid := Coordinator_TransactionReq();
    par YieldInv_8() | YieldConsistent_9() | YieldConsistent_10() | YieldConsistent_11();
  }
  yield;
}

// ###########################################################################
// Event Handlers

procedure {:layer 0,10} {:inline 1} GhostRead() returns (snapshot: GState)
{
   snapshot := state;
}

procedure {:atomic} {:layer 11} atomic_Coordinator_TransactionReq () returns (xid: Xid)
modifies state;
{
  var newState: XState;
  assume xConsistent(newState);
  state[xid]:= newState;
} 
  
procedure {:yields} {:layer 10} {:refines "atomic_Coordinator_TransactionReq"} Coordinator_TransactionReq () returns (xid: Xid)
requires {:layer 8} Inv_8(state, B, votes);
ensures  {:layer 8} Inv_8(state, B, votes);
requires {:layer 9,10} gConsistent(state);
ensures  {:layer 9,10} gConsistent(state);
{
  var {:linear "pair"} pair: Pair;
  var {:linear "pair"} pairs: [Pair]bool;
  var {:layer 10} snapshot: GState;
  var i : Mid;
  
  par YieldInv_8() | YieldConsistent_9() | YieldConsistent_10();
  call xid, pairs := AllocateXid();
  assert {:layer 10} NextStateTrigger(state[xid]);
  call snapshot := GhostRead();
  i := 1;
  while (i <= numParticipants)
  invariant {:terminates} {:layer 8,9,10} true;
  invariant {:layer 8} Inv_8(state, B, votes);
  invariant {:layer 8,10} pairs == (lambda p: Pair :: pair(xid, mid#Pair(p), p) && i <= mid#Pair(p));
  invariant {:layer 8} votes[xid] == -1 || (forall p: Pair :: pairs[p] ==> UndecidedOrCommitted(state[xid][mid#Pair(p)]));
  invariant {:layer 9} Inv_9(state, B, xid);
  invariant {:layer 10} gConsistent(state);
  invariant {:layer 10} ExistsMonotoneExtension(snapshot, state, xid);
  invariant {:layer 8,10} 1 <= i && i <= numParticipants + 1;
  {
    call pairs, pair := TransferPair(xid, i, pairs);
    async call Participant_VoteReq(xid, i, pair);
    i := i + 1;
    par YieldPairs_8(xid, pairs) | YieldInv_9(xid);
    assert {:layer 10} NextStateTrigger(state[xid]);
  }
  par YieldInv_8() | YieldConsistent_9() | YieldConsistent_10();
}

// ---------------------------------------------------------------------------

procedure {:left} {:layer 10} atomic_Participant_VoteReq (xid: Xid, mid: Mid, {:linear_in "pair"} pair: Pair)
modifies state;
{
  var oldState, newState: XState;
  assert !UnallocatedXids[xid];
  assert pair(xid, mid, pair);
  assert xConsistent(state[xid]);
  oldState := state[xid];
  assume xConsistentExtension(oldState, newState);
  state[xid] := newState;
}          

procedure {:yields} {:layer 9} {:refines "atomic_Participant_VoteReq"} Participant_VoteReq (xid: Xid, mid: Mid, {:linear_in "pair"} pair: Pair)
requires {:layer 8} Inv_8(state, B, votes) && pair(xid, mid, pair) && (votes[xid] == -1 || UndecidedOrCommitted(state[xid][mid]));
requires {:layer 9} Inv_9(state, B, xid);
{
  par YieldUndecidedOrCommitted_8(xid, mid, pair) | YieldInv_9(xid);

  if (*) {
    async call Coordinator_VoteYes(xid, mid, pair);
  } else {
    call SetParticipantAborted(xid, mid, pair);
    async call Coordinator_VoteNo(xid, mid, pair);
  }

  yield;
}

// ---------------------------------------------------------------------------

function {:inline} Inv_9 (state: GState, B: [Pair]bool, xid: Xid) : bool
{
     gConsistent(state)
  && (xAllParticipantsInB(xid, B) || xUndecidedOrAborted(state[xid]))
}

function {:inline} SetInv (B: [Pair]bool) : bool
{
  (forall xid: Xid, mid: Mid :: B[Pair(xid,mid)] ==> participantMid(mid))
}

function {:inline} Inv_8 (state: GState, B: [Pair]bool, votes: [Xid]int) : bool
{
     gConsistent(state)
  && SetInv(B)
  && (forall xid: Xid :: {XidTrigger(xid)} XidTrigger(xid) ==> VotesEqCoordinatorState(votes, state, xid))
  && (forall xid: Xid :: {XidTrigger(xid)} XidTrigger(xid) ==> votes[xid] == -1 || votes[xid] == card(B, xid))
  && (forall p: Pair :: B[p] && votes[xid#Pair(p)] != -1 ==> UndecidedOrCommitted(state[xid#Pair(p)][mid#Pair(p)]))
}

procedure {:left} {:layer 9} atomic_Coordinator_VoteYes (xid: Xid, mid: Mid, {:linear_in "pair"} pair: Pair)
modifies state, B;
{
  var oldState, newState: XState;
  assert !UnallocatedXids[xid];
  assert pair(xid, mid, pair);
  assert xConsistent(state[xid]);
  B[pair] := true;
  oldState := state[xid];
  if (*) {
    assume xAllParticipantsInB(xid, B);
    assume xConsistentExtension(oldState, newState);
    state[xid] := newState;
  } 
}

procedure {:yields} {:layer 8} {:refines "atomic_Coordinator_VoteYes"} Coordinator_VoteYes (xid: Xid, mid: Mid, {:linear_in "pair"} pair: Pair)
requires {:layer 8} Inv_8(state, B, votes) && pair(xid, mid, pair) && (votes[xid] == -1 || UndecidedOrCommitted(state[xid][mid]));
{
  var commit : bool;
  var i : Mid;
  var {:layer 8} snapshot: GState;

  call YieldUndecidedOrCommitted_8(xid, mid, pair);
  assert {:layer 8} XidTrigger(xid);
  call snapshot := GhostRead();
  call Lemma_add_to_B(pair);
  call Lemma_all_in_B(xid);
  call commit := StateUpdateOnVoteYes(xid, mid, pair);
  call Lemma_all_in_B(xid);
  assert {:layer 8} XidTrigger(xid);
  assert {:layer 8} NextStateTrigger(state[xid]);
  
  if (commit)
  {
    assert {:layer 8} xUndecidedOrCommitted(snapshot[xid]);
    assert {:layer 8} xUndecidedOrCommitted(state[xid]);
    i := 1;
    while (i <= numParticipants)
    invariant {:layer 7,8} {:terminates} true;
    invariant {:layer 8} 1 <= i && i <= numParticipants + 1;
    invariant {:layer 8} Inv_8(state, B, votes);
    invariant {:layer 8} ExistsMonotoneExtension(snapshot, state, xid);
    {
      async call Participant_Commit(xid, i);
      i := i + 1;
      assert {:layer 8} XidTrigger(xid);
      assert {:layer 8} NextStateTrigger(state[xid]);
    }
  }
  assert {:layer 8} XidTrigger(xid);
  assert {:layer 8} NextStateTrigger(state[xid]);
  yield;
}

procedure {:left} {:layer 9} atomic_Coordinator_VoteNo (xid: Xid, mid: Mid, {:linear_in "pair"} pair: Pair)
modifies state;
{
  var oldState, newState: XState;
  assert !UnallocatedXids[xid];
  assert pair(xid, mid, pair);
  assert xUndecidedOrAborted(state[xid]);
  oldState := state[xid];
  assume xUndecidedOrAborted(newState);
  assume xConsistentExtension(oldState, newState);
  state[xid] := newState;
}

procedure {:yields} {:layer 8} {:refines "atomic_Coordinator_VoteNo"} Coordinator_VoteNo (xid: Xid, mid: Mid, {:linear_in "pair"} pair: Pair)
requires {:layer 8} Inv_8(state, B, votes) && pair(xid, mid, pair) && Aborted(state[xid][mid]);
{
  var abort : bool;
  var i : int;
  var {:layer 8} snapshot: GState;

  call YieldAborted_8(xid, mid, pair);
  call snapshot := GhostRead();
  call abort := StateUpdateOnVoteNo(xid, mid);
  assert {:layer 8} XidTrigger(xid);
  assert {:layer 8} NextStateTrigger(state[xid]);
  
  if (abort)
  {
    i := 1;
    while (i <= numParticipants)
    invariant {:layer 7,8} {:terminates} true;
    invariant {:layer 8} 1 <= i && i <= numParticipants + 1;
    invariant {:layer 8} Aborted(state[xid][CoordinatorMid]);
    invariant {:layer 8} xUndecidedOrAborted(state[xid]);
    invariant {:layer 8} Inv_8(state, B, votes);
    invariant {:layer 8} ExistsMonotoneExtension(snapshot, state, xid);
    {
      async call Participant_Abort(xid, i);
      i := i + 1;
      assert {:layer 8} XidTrigger(xid);
      assert {:layer 8} NextStateTrigger(state[xid]);
    }
  }
  assert {:layer 8} XidTrigger(xid);
  assert {:layer 8} NextStateTrigger(state[xid]);
  yield;
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
  pairs := (lambda p: Pair :: pair(xid, mid#Pair(p), p));
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

function {:builtin "MapConst"} MapConstBool(bool): [Pair]bool;
function {:builtin "MapOr"} MapOr([Pair]bool, [Pair]bool) : [Pair]bool;

function {:inline} {:linear "pair"} PairCollector(x: Pair) : [Pair]bool
{
  MapConstBool(false)[x := true]
}
function {:inline} {:linear "pair"} PairSetCollector(x: [Pair]bool) : [Pair]bool
{
  x
}
function {:inline} {:linear "pair"} XidSetCollector(xids: [Xid]bool) : [Pair]bool
{
  (lambda p: Pair :: xids[xid#Pair(p)])
}

// ############################################################################
// Lemmas about cardinality

function card(pairs: [Pair]bool, xid: Xid) : int;

procedure {:layer 8} Lemma_add_to_B (pair: Pair);
requires participantMid(mid#Pair(pair));
requires !B[pair];
ensures (forall xid: Xid :: card(B[pair := true], xid) == (if xid == xid#Pair(pair) then card(B, xid) + 1 else card(B, xid)));

procedure {:layer 8} Lemma_all_in_B (xid: Xid);
requires SetInv(B);
ensures card(B, xid) >= numParticipants ==> (forall mid: Mid :: {participantMid(mid)} participantMid(mid) ==> B[Pair(xid, mid)]);

