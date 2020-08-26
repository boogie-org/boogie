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

type {:datatype} OptionValue;
function {:constructor} SomeValue(value: Value): OptionValue;
function {:constructor} NoneValue(): OptionValue;

type {:datatype} OptionVoteInfo;
function {:constructor} NoneVoteInfo(): OptionVoteInfo;
function {:constructor} SomeVoteInfo(value: Value, ns: NodeSet): OptionVoteInfo;

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

type {:datatype} Permission;
function {:constructor} JoinPerm(r:Round, n: Node): Permission;
function {:constructor} VotePerm(r:Round, n: Node): Permission;
function {:constructor} ConcludePerm(r: Round): Permission;

type {:pending_async}{:datatype} PA;
function {:pending_async "A_StartRound"}{:constructor} StartRound_PA(round: Round, round_lin: Round) : PA;
function {:pending_async "A_Join"}{:constructor} Join_PA(round: Round, node: Node, p: Permission) : PA;
function {:pending_async "A_Propose"}{:constructor} Propose_PA(round: Round, ps: [Permission]bool) : PA;
function {:pending_async "A_Vote"}{:constructor} Vote_PA(round: Round, node: Node, value: Value, p: Permission) : PA;
function {:pending_async "A_Conclude"}{:constructor} Conclude_PA(round: Round, value: Value, p: Permission) : PA;

////////////////////////////////////////////////////////////////////////////////
//// Generalized array theory imports

function {:builtin "MapConst"} MapConstPermission(bool): [Permission]bool;
function {:builtin "MapOr"} MapOrPermission([Permission]bool, [Permission]bool): [Permission]bool;
function {:builtin "MapConst"} MapConstNode(bool): NodeSet;
function {:builtin "MapOr"} MapOrNode(NodeSet, NodeSet): NodeSet;
function {:builtin "MapAnd"} MapAndNode(NodeSet, NodeSet): NodeSet;
function {:builtin "MapImp"} MapImpNode(NodeSet, NodeSet) : NodeSet;
function {:builtin "MapConst"} MapConstPA(int): [PA]int;
function {:builtin "MapAdd"} MapAddPA([PA]int, [PA]int): [PA]int;
function {:builtin "MapSub"} MapSubPA([PA]int, [PA]int): [PA]int;
function {:builtin "MapConst"} MapConstBool(bool) : [Permission]bool;
function {:builtin "MapOr"} MapOr([Permission]bool, [Permission]bool) : [Permission]bool;
function {:builtin "MapConst"} MapConstVoteResponse(int): [VoteResponse]int;
function {:builtin "MapAdd"} MapAddVoteResponse([VoteResponse]int, [VoteResponse]int): [VoteResponse]int;
function {:builtin "MapSub"} MapSubVoteResponse([VoteResponse]int, [VoteResponse]int): [VoteResponse]int;

////////////////////////////////////////////////////////////////////////////////
//// Functions

function {:inline} NoPAs(): [PA]int { MapConstPA(0) }
function {:inline} SingletonPA(pa:PA): [PA]int { NoPAs()[pa := 1] }

function {:inline} NoNodes(): NodeSet { MapConstNode(false) }
function {:inline} SingletonNode(node: Node): NodeSet { NoNodes()[node := true] }

function Cardinality(q: NodeSet): int;
axiom Cardinality(NoNodes()) == 0;

function IsQuorum(ns: NodeSet): bool {
  2 * Cardinality(ns) > numNodes &&
  (forall n: Node :: ns[n] ==> Node(n))
}

function {:inline} IsSubset(ns1:NodeSet, ns2:NodeSet) : bool {
  MapImpNode(ns1, ns2) == MapConstNode(true)
}

function {:inline} IsDisjoint(ns1:NodeSet, ns2:NodeSet) : bool {
  MapAndNode(ns1, ns2) == MapConstNode(false)
}

// MaxRound(r, ns, voteInfo) returns the highest round less than r that some node in ns voted for.
// If no node in ns has voted for a round less than r, then it returns 0.
function MaxRound(r: Round, ns: NodeSet, voteInfo: [Round]OptionVoteInfo): int;
axiom (forall r: Round, ns: NodeSet, voteInfo: [Round]OptionVoteInfo :: { MaxRound(r, ns, voteInfo) }
  Round(r) ==>
  (
    var ret := MaxRound(r, ns, voteInfo);
    0 <= ret && ret < r &&
    (forall r': Round :: ret < r' && r' < r && is#SomeVoteInfo(voteInfo[r']) ==> IsDisjoint(ns, ns#SomeVoteInfo(voteInfo[r']))) &&
    (Round(ret) ==> is#SomeVoteInfo(voteInfo[ret]) && !IsDisjoint(ns, ns#SomeVoteInfo(voteInfo[ret])))
  )
);

function {:inline} Lemma_MaxRound_InitVote(voteInfo: [Round]OptionVoteInfo, r: Round, r': Round) : bool
{
  (forall ns: NodeSet, v': Value ::
    is#NoneVoteInfo(voteInfo[r']) ==>
      MaxRound(r, ns, voteInfo) ==
      MaxRound(r, ns, voteInfo[r' := SomeVoteInfo(v', NoNodes())]))
}

function {:inline} Lemma_MaxRound_AddNodeToVote(voteInfo: [Round]OptionVoteInfo, r: Round, r': Round, n: Node) : bool
{
  (forall ns: NodeSet ::
    is#SomeVoteInfo(voteInfo[r']) && (!ns[n] || r <= r') ==>
    (
      var v', ns' := value#SomeVoteInfo(voteInfo[r']), ns#SomeVoteInfo(voteInfo[r']);
      MaxRound(r, ns, voteInfo) ==
      MaxRound(r, ns, voteInfo[r' := SomeVoteInfo(v', ns'[n:=true])])
    )
  )
}

function {:inline} JoinPermissions(r: Round) : [Permission]bool
{
  (lambda p:Permission :: if (is#JoinPerm(p) && r#JoinPerm(p) == r) then true else false)
}

function {:inline} ProposePermissions(r: Round) : [Permission]bool
{
  (lambda p:Permission :: if (is#VotePerm(p) && r#VotePerm(p) == r) || (is#ConcludePerm(p) && r#ConcludePerm(p) == r) then true else false)
}

function {:inline} VotePermissions(r: Round) : [Permission]bool
{
  (lambda p:Permission :: if (is#VotePerm(p) && r#VotePerm(p) == r) then true else false)
}

function {:inline} JoinPAs(r: Round) : [PA]int
{
  (lambda pa: PA :: if is#Join_PA(pa) && round#Join_PA(pa) == r && Node(node#Join_PA(pa)) && p#Join_PA(pa) == JoinPerm(r, node#Join_PA(pa)) then 1 else 0)
}

function {:inline} VotePAs(r: Round, v: Value) : [PA]int
{
  (lambda pa: PA :: if is#Vote_PA(pa) && round#Vote_PA(pa) == r && Node(node#Vote_PA(pa)) && value#Vote_PA(pa) == v && p#Vote_PA(pa) == VotePerm(r, node#Vote_PA(pa)) then 1 else 0)
}

////////////////////////////////////////////////////////////////////////////////
//// Global variables
// Abstract
var {:layer 1,3} joinedNodes: [Round]NodeSet;
var {:layer 1,3} voteInfo: [Round]OptionVoteInfo;
var {:layer 1,3} pendingAsyncs: [PA]int;

// Concrete
var {:layer 0,1} acceptorState: [Node]AcceptorState;
var {:layer 0,1} joinChannel: [Round][JoinResponse]int;
var {:layer 0,1} voteChannel: [Round][VoteResponse]int;
var {:layer 0,3} decision: [Round]OptionValue; // spec

// Intermediate channel representation
var {:layer 1,1} {:linear "perm"} permJoinChannel: JoinResponseChannel;
var {:layer 1,1} {:linear "perm"} permVoteChannel: VoteResponseChannel;

////////////////////////////////////////////////////////////////////////////////

function {:inline} Init (
  rs: [Round]bool, joinedNodes:[Round]NodeSet, voteInfo: [Round]OptionVoteInfo,
  decision:[Round]OptionValue, pendingAsyncs: [PA]int) : bool
{
  rs == (lambda r: Round :: true) &&
  (forall r: Round :: joinedNodes[r] == NoNodes()) &&
  (forall r: Round :: is#NoneVoteInfo(voteInfo[r])) &&
  (forall r: Round :: is#NoneValue(decision[r])) &&
  (forall pa: PA :: pendingAsyncs[pa] == 0)
}

function {:inline} InitLow (
  acceptorState: [Node]AcceptorState,
  joinChannel: [Round][JoinResponse]int,
  voteChannel: [Round][VoteResponse]int,
  permJoinChannel: JoinResponseChannel,
  permVoteChannel: VoteResponseChannel) : bool
{
  (forall n: Node :: lastJoinRound#AcceptorState(acceptorState[n]) == 0 && lastVoteRound#AcceptorState(acceptorState[n]) == 0) &&
  (forall r: Round, jr: JoinResponse :: joinChannel[r][jr] == 0) &&
  (forall r: Round, vr: VoteResponse :: voteChannel[r][vr] == 0) &&
  domain#JoinResponseChannel(permJoinChannel) == MapConstPermission(false) &&
  domain#VoteResponseChannel(permVoteChannel) == MapConstPermission(false)
}

////////////////////////////////////////////////////////////////////////////////
//// Linear collectors

function {:inline}{:linear "perm"} PermissionCollector (p: Permission) : [Permission]bool
{
  MapConstBool(false)[p := true]
}

function {:inline}{:linear "perm"} PermissionSetCollector (ps: [Permission]bool) : [Permission]bool
{
  ps
}

function {:inline}{:linear "perm"} RoundCollector (round: Round) : [Permission]bool
{
  (lambda p: Permission ::
    if (is#JoinPerm(p) && round == r#JoinPerm(p)) ||
       (is#VotePerm(p) && round == r#VotePerm(p)) ||
       (is#ConcludePerm(p) && round == r#ConcludePerm(p))
    then true else false
  )
}

function {:inline}{:linear "perm"} RoundSetCollector (rounds: [Round]bool) : [Permission]bool
{
  (lambda p: Permission ::
    if (is#JoinPerm(p) && rounds[r#JoinPerm(p)]) ||
       (is#VotePerm(p) && rounds[r#VotePerm(p)]) ||
       (is#ConcludePerm(p) && rounds[r#ConcludePerm(p)])
    then true else false
  )
}

function {:inline}{:linear "perm"} JoinResponseChannelCollector (permJoinChannel: JoinResponseChannel) : [Permission]bool
{
  domain#JoinResponseChannel(permJoinChannel)
}

function {:inline}{:linear "perm"} VoteResponseChannelCollector (permVoteChannel: VoteResponseChannel) : [Permission]bool
{
  domain#VoteResponseChannel(permVoteChannel)
}
////////////////////////////////////////////////////////////////////////////////
//// Trigger dummies

function triggerRound(r: Round) : bool { true }
function triggerNode(n: Node) : bool { true }
