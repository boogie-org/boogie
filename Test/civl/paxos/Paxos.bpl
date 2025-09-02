////////////////////////////////////////////////////////////////////////////////
//// Types and constants
const numNodes: int;
axiom numNodes > 0;

type Round = int;
function Round(x: int): bool { 1 <= x }

type Node = int;
function Node(x: int): bool { 1 <= x && x <= numNodes }

type NodeSet = [Node]bool;

type Value;

/* 0 <= lastVoteRound, lastJoinRound <= numRounds */
datatype AcceptorState { AcceptorState(lastJoinRound: Round, lastVoteRound: int, lastVoteValue: Value) }

/* 0 <= lastVoteRound <= numRounds */
datatype JoinResponse {
  JoinAccept(from: Node, lastVoteRound: int, lastVoteValue: Value),
  JoinReject(from: Node)
}

datatype VoteResponse {
  VoteAccept(from: Node),
  VoteReject(from: Node)
}

datatype Permission {
  RoundPerm(r: Round),
  JoinPerm(r: Round, n: Node),
  VotePerm(r: Round, n: Node)
}

datatype RoundStatus {
  Inactive(),
  Proposed(value: Value),
  Decided(value: Value)
}

////////////////////////////////////////////////////////////////////////////////
//// Functions

function {:inline} IsActive(rs: RoundStatus, v: Value): bool { rs == Proposed(v) || rs == Decided(v) }
function {:inline} NoNodes(): NodeSet { MapConst(false) }
function {:inline} SingletonNode(node: Node): NodeSet { NoNodes()[node := true] }

function {:inline} AllPermissions(r: Round) : Set Permission
{
  Set((lambda {:pool "Permission"} p:Permission :: {:add_to_pool "Permission", p} p->r == r))
}

function {:inline} JoinPermissions(r: Round) : Set Permission
{
  Set((lambda {:pool "Permission"} p:Permission :: {:add_to_pool "Permission", p} p is JoinPerm && p->r == r && Node(p->n)))
}

function {:inline} VotePermissions(r: Round) : Set Permission
{
  Set((lambda {:pool "Permission"} p:Permission :: {:add_to_pool "Permission", p} p is VotePerm && p->r == r && Node(p->n)))
}

function {:inline} JoinPermissionsUpto(r: Round, n: Node) : Set Permission
{
  Set((lambda {:pool "Permission"} p:Permission :: {:add_to_pool "Permission", p} p is JoinPerm && p->r == r && Node(p->n) && p->n < n))
}

function {:inline} VotePermissionsUpto(r: Round, n: Node) : Set Permission
{
  Set((lambda {:pool "Permission"} p:Permission :: {:add_to_pool "Permission", p} p is VotePerm && p->r == r && Node(p->n) && p->n < n))
}

function {:inline} ToVotePermissions(r: Round, ns: NodeSet): Set Permission
{
  Set((lambda p: Permission:: p is VotePerm && p->r == r && ns[p->n]))
}

function IsJoinQuorum(r: Round, ps: Set Permission): bool
{
  2 * Set_Size(ps) > numNodes && Set_IsSubset(ps, JoinPermissions(r))
}

function IsVoteQuorum(r: Round, ps: Set Permission): bool
{
  2 * Set_Size(ps) > numNodes && Set_IsSubset(ps, VotePermissions(r))
}

function {:inline} VoteQuorumLt(r: Round, status: [Round]RoundStatus, voteInfo: [Round]NodeSet): bool
{
  (forall r': Round:: Round(r') && r' < r && status[r'] is Decided ==> IsVoteQuorum(r', ToVotePermissions(r', voteInfo[r'])))
}

function {:inline} VoteQuorumLe(r: Round, status: [Round]RoundStatus, voteInfo: [Round]NodeSet): bool
{
  (forall r': Round:: Round(r') && r' <= r && status[r'] is Decided ==> IsVoteQuorum(r', ToVotePermissions(r', voteInfo[r'])))
}

function {:inline} SpecLt(r: Round, status: [Round]RoundStatus): bool
{
  (forall r1, r2: Round:: Round(r1) && r1 <= r2 && r2 < r && status[r1] is Decided ==> status[r2] is Inactive || status[r1]->value == status[r2]->value)
}

function {:inline} SpecLe(r: Round, status: [Round]RoundStatus): bool
{
  (forall r1, r2: Round:: Round(r1) && r1 <= r2 && r2 <= r && status[r1] is Decided ==> status[r2] is Inactive || status[r1]->value == status[r2]->value)
}

////////////////////////////////////////////////////////////////////////////////
//// Global variables

var {:layer 1,2} status: [Round]RoundStatus;
var {:layer 1,2} joinInfo: [Round]NodeSet;
var {:layer 1,2} voteInfo: [Round]NodeSet;

var {:layer 1,2} {:linear} joinChannelPermissions: Set Permission;
var {:layer 1,2} {:linear} voteChannelPermissions: Set Permission;
var {:layer 1,2} {:linear} usedPermissions: Set Permission;

var {:layer 0,1} acceptorState: [Node]AcceptorState;
var {:layer 0,1} joinChannel: [Round][JoinResponse]int;
var {:layer 0,1} voteChannel: [Round][VoteResponse]int;

////////////////////////////////////////////////////////////////////////////////
//// Invariants

// MaxRound(r, n, voteInfo) returns the highest round less than r that n voted for.
// If n has not voted for a round less than r, then 0 is returned.
function MaxRound(r: Round, n: Node, voteInfo: [Round]NodeSet): int;
axiom (forall r: Round, n: Node, voteInfo: [Round]NodeSet :: {MaxRound(r, n, voteInfo)}
  Round(r) ==> MaxRoundPredicate(r, n, voteInfo, MaxRound(r, n, voteInfo))
);

function {:inline} MaxRoundPredicate(r: Round, n: Node, voteInfo: [Round]NodeSet, maxRound: int): bool
{
  0 <= maxRound && maxRound < r &&
  (forall r': Round :: maxRound < r' && r' < r ==> !voteInfo[r'][n]) &&
  (maxRound == 0 || voteInfo[maxRound][n])
}

function {:inline} Inv(status: [Round]RoundStatus, joinInfo: [Round]NodeSet, voteInfo: [Round]NodeSet, acceptorState: [Node]AcceptorState,
              joinChannel: [Round][JoinResponse]int, joinChannelPermissions: Set Permission,
              voteChannel: [Round][VoteResponse]int, voteChannelPermissions: Set Permission) : bool
{
  (forall r: Round, jr: JoinResponse :: 0 <= joinChannel[r][jr] && joinChannel[r][jr] <= 1)
  &&
  (forall r: Round, jr1: JoinResponse, jr2: JoinResponse :: jr1->from == jr2->from && joinChannel[r][jr1] > 0 && joinChannel[r][jr2] > 0 ==> jr1 == jr2)
  &&
  (forall r: Round, jr: JoinResponse :: joinChannel[r][jr] > 0 ==> 
    Round(r) && Node(jr->from) && Set_Contains(joinChannelPermissions, JoinPerm(r, jr->from)) &&
    (jr is JoinAccept ==> joinInfo[r][jr->from] &&
                          MaxRoundPredicate(r, jr->from, voteInfo, jr->lastVoteRound) &&
                          r <= acceptorState[jr->from]->lastJoinRound &&
                          (jr->lastVoteRound == 0 || IsActive(status[jr->lastVoteRound], jr->lastVoteValue)))
  )

  &&
  (forall r: Round, vr: VoteResponse :: 0 <= voteChannel[r][vr] && voteChannel[r][vr] <= 1)
  &&
  (forall r: Round, vr1: VoteResponse, vr2: VoteResponse :: vr1->from == vr2->from && voteChannel[r][vr1] > 0 && voteChannel[r][vr2] > 0 ==> vr1 == vr2)
  &&
  (forall r: Round, vr: VoteResponse :: voteChannel[r][vr] > 0 ==> Round(r) && Node(vr->from) && Set_Contains(voteChannelPermissions, VotePerm(r, vr->from)) &&
    (vr is VoteAccept <==> voteInfo[r][vr->from])
  )

  &&
  (forall n: Node :: Node(n) ==>
    (
      var lastJoinRound, lastVoteRound, lastVoteValue := acceptorState[n]->lastJoinRound, acceptorState[n]->lastVoteRound, acceptorState[n]->lastVoteValue;
      lastVoteRound <= lastJoinRound &&
      (lastJoinRound == 0 || (Round(lastJoinRound) && joinInfo[lastJoinRound][n])) &&
      (forall r: Round :: lastJoinRound < r && Round(r) ==> !joinInfo[r][n]) &&
      (lastVoteRound == 0 || (Round(lastVoteRound) && voteInfo[lastVoteRound][n] && IsActive(status[lastVoteRound], lastVoteValue))) &&
      (forall r: Round :: lastVoteRound < r && Round(r) ==> !voteInfo[r][n])
    )
  )
}

yield invariant {:layer 1} YieldInv();
preserves Inv(status, joinInfo, voteInfo, acceptorState, joinChannel, joinChannelPermissions, voteChannel, voteChannelPermissions);

////////////////////////////////////////////////////////////////////////////////
//// Quorum

pure procedure Lemma_Quorum_Intersection(r: Round, joinAcceptPerms: Set Permission, status: [Round]RoundStatus, voteInfo: [Round]NodeSet);
requires Round(r);
requires IsJoinQuorum(r, joinAcceptPerms);
requires VoteQuorumLt(r, status, voteInfo);
ensures  (forall r': Round:: Round(r') && r' < r && status[r'] is Decided ==>
            (exists n: Node:: Node(n) && Set_Contains(joinAcceptPerms, JoinPerm(r, n)) && voteInfo[r'][n]));

pure procedure Lemma_Quorum_Monotonic(r: Round, voteAcceptPerms: Set Permission, ns: NodeSet);
requires Round(r);
requires IsVoteQuorum(r, voteAcceptPerms);
requires Set_IsSubset(voteAcceptPerms, ToVotePermissions(r, ns));
ensures IsVoteQuorum(r, ToVotePermissions(r, ns));