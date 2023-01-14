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

type {:datatype} Option _;
function {:constructor} None<T>(): Option T;
function {:constructor} Some<T>(t: T): Option T;

type {:datatype} VoteInfo;
function {:constructor} VoteInfo(value: Value, ns: NodeSet): VoteInfo;

type {:datatype} AcceptorState;
/* 0 <= lastVoteRound, lastJoinRound <= numRounds */
function {:constructor} AcceptorState(lastJoinRound: Round, lastVoteRound: int, lastVoteValue: Value): AcceptorState;

type {:datatype} JoinResponse;
/* 0 <= lastVoteRound <= numRounds */
function {:constructor} JoinResponse(from: Node, lastVoteRound: int, lastVoteValue: Value): JoinResponse;
type {:datatype} JoinResponseChannel;
function {:constructor} JoinResponseChannel(domain: [Permission]bool, contents: [Permission]JoinResponse): JoinResponseChannel;

type {:datatype} VoteResponse;
function {:constructor} VoteResponse(from: Node): VoteResponse;
type {:datatype} VoteResponseChannel;
function {:constructor} VoteResponseChannel(domain: [Permission]bool, contents: [Permission]VoteResponse): VoteResponseChannel;

type {:datatype} {:linear "perm"} Permission;
function {:constructor} JoinPerm(r:Round, n: Node): Permission;
function {:constructor} VotePerm(r:Round, n: Node): Permission;
function {:constructor} ConcludePerm(r: Round): Permission;

type {:pending_async}{:datatype} PA;
function {:constructor} A_StartRound(r: Round, r_lin: Round) : PA;
function {:constructor} A_Join(r: Round, n: Node, p: Permission) : PA;
function {:constructor} A_Propose(r: Round, ps: [Permission]bool) : PA;
function {:constructor} A_Vote(r: Round, n: Node, v: Value, p: Permission) : PA;
function {:constructor} A_Conclude(r: Round, v: Value, p: Permission) : PA;

////////////////////////////////////////////////////////////////////////////////
//// Functions

function {:inline} NoPAs(): [PA]int { MapConst(0) }
function {:inline} SingletonPA(pa:PA): [PA]int { NoPAs()[pa := 1] }

function {:inline} NoNodes(): NodeSet { MapConst(false) }
function {:inline} SingletonNode(node: Node): NodeSet { NoNodes()[node := true] }

function Cardinality(q: NodeSet): int;
axiom Cardinality(NoNodes()) == 0;

function IsQuorum(ns: NodeSet): bool {
  2 * Cardinality(ns) > numNodes &&
  (forall n: Node :: ns[n] ==> Node(n))
}

axiom (forall ns1: NodeSet, ns2: NodeSet ::
  IsQuorum(ns1) && IsQuorum(ns2) ==> (exists n: Node :: Node(n) && ns1[n] && ns2[n])
);

function {:inline} IsSubset(ns1:NodeSet, ns2:NodeSet) : bool {
  MapImp(ns1, ns2) == MapConst(true)
}

function {:inline} IsDisjoint(ns1:NodeSet, ns2:NodeSet) : bool {
  MapAnd(ns1, ns2) == MapConst(false)
}

// MaxRound(r, ns, voteInfo) returns the highest round less than r that some node in ns voted for.
// If no node in ns has voted for a round less than r, then it returns 0.
function MaxRound(r: Round, ns: NodeSet, voteInfo: [Round]Option VoteInfo): int;
axiom (forall r: Round, ns: NodeSet, voteInfo: [Round]Option VoteInfo ::
  Round(r) ==>
  (
    var ret := MaxRound(r, ns, voteInfo);
    0 <= ret && ret < r &&
    (forall r': Round :: ret < r' && r' < r && voteInfo[r'] is Some ==> IsDisjoint(ns, voteInfo[r']->t->ns)) &&
    (Round(ret) ==> voteInfo[ret] is Some && !IsDisjoint(ns, voteInfo[ret]->t->ns))
  )
);

function {:inline} JoinPermissions(r: Round) : [Permission]bool
{
  (lambda p:Permission :: if (p is JoinPerm && p->r == r) then true else false)
}

function {:inline} ProposePermissions(r: Round) : [Permission]bool
{
  (lambda {:pool "Permission"} p:Permission :: if (p is VotePerm && p->r == r) || (p is ConcludePerm && p->r == r) then true else false)
}

function {:inline} VotePermissions(r: Round) : [Permission]bool
{
  (lambda p:Permission :: if (p is VotePerm && p->r == r) then true else false)
}

function {:inline} JoinPAs(r: Round) : [PA]int
{
  (lambda pa: PA :: if pa is A_Join && pa->r == r && Node(pa->n) && pa->p == JoinPerm(r, pa->n) then 1 else 0)
}

function {:inline} VotePAs(r: Round, v: Value) : [PA]int
{
  (lambda pa: PA :: if pa is A_Vote && pa->r == r && Node(pa->n) && pa->v == v && pa->p == VotePerm(r, pa->n) then 1 else 0)
}

////////////////////////////////////////////////////////////////////////////////
//// Global variables
// Abstract
var {:layer 1,3} joinedNodes: [Round]NodeSet;
var {:layer 1,3} voteInfo: [Round]Option VoteInfo;
var {:layer 1,3} pendingAsyncs: [PA]int;

// Concrete
var {:layer 0,1} acceptorState: [Node]AcceptorState;
var {:layer 0,1} joinChannel: [Round][JoinResponse]int;
var {:layer 0,1} voteChannel: [Round][VoteResponse]int;
var {:layer 0,3} decision: [Round]Option Value; // spec

// Intermediate channel representation
var {:layer 1,1} {:linear "perm"} permJoinChannel: JoinResponseChannel;
var {:layer 1,1} {:linear "perm"} permVoteChannel: VoteResponseChannel;

////////////////////////////////////////////////////////////////////////////////

function {:inline} Init (
  rs: [Round]bool, joinedNodes:[Round]NodeSet, voteInfo: [Round]Option VoteInfo,
  decision:[Round]Option Value, pendingAsyncs: [PA]int) : bool
{
  rs == (lambda r: Round :: true) &&
  (forall r: Round :: joinedNodes[r] == NoNodes()) &&
  (forall r: Round :: voteInfo[r] is None) &&
  (forall r: Round :: decision[r] is None) &&
  (forall pa: PA :: pendingAsyncs[pa] == 0)
}

function {:inline} InitLow (
  acceptorState: [Node]AcceptorState,
  joinChannel: [Round][JoinResponse]int,
  voteChannel: [Round][VoteResponse]int,
  permJoinChannel: JoinResponseChannel,
  permVoteChannel: VoteResponseChannel) : bool
{
  (forall n: Node :: acceptorState[n]->lastJoinRound == 0 && acceptorState[n]->lastVoteRound == 0) &&
  (forall r: Round, jr: JoinResponse :: joinChannel[r][jr] == 0) &&
  (forall r: Round, vr: VoteResponse :: voteChannel[r][vr] == 0) &&
  permJoinChannel->domain == MapConst(false) &&
  permVoteChannel->domain == MapConst(false)
}

////////////////////////////////////////////////////////////////////////////////
//// Linear collectors

function {:inline}{:linear "perm"} RoundCollector (round: Round) : [Permission]bool
{
  (lambda {:pool "Permission"} p: Permission :: round == p->r)
}

function {:inline}{:linear "perm"} RoundSetCollector (rounds: [Round]bool) : [Permission]bool
{
  (lambda {:pool "Permission"} p: Permission :: rounds[p->r])
}

function {:inline}{:linear "perm"} JoinResponseChannelCollector (permJoinChannel: JoinResponseChannel) : [Permission]bool
{
  permJoinChannel->domain
}

function {:inline}{:linear "perm"} VoteResponseChannelCollector (permVoteChannel: VoteResponseChannel) : [Permission]bool
{
  permVoteChannel->domain
}
