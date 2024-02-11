function Inv (joinedNodes: [Round]NodeSet, voteInfo: [Round]Option VoteInfo, acceptorState: [Node]AcceptorState,
              permJoinChannel: JoinResponseChannel, permVoteChannel: VoteResponseChannel) : bool
{
  (forall p: Permission :: permJoinChannel->dom->val[p] ==> p is JoinPerm &&
    (var r, n, joinResponse := p->r, p->n, permJoinChannel->val[p];
      Round(r) && Node(n) &&
      (
        var from, maxRound, maxValue := joinResponse->from, joinResponse->lastVoteRound, joinResponse->lastVoteValue;
        n == from &&
        joinedNodes[r][from] &&
        0 <= maxRound && maxRound < r &&
        (maxRound == 0 || (voteInfo[maxRound] is Some && voteInfo[maxRound]->t->ns[from] && voteInfo[maxRound]->t->value == maxValue)) &&
        (forall r': Round :: maxRound < r' && r' < r && voteInfo[r'] is Some ==> !voteInfo[r']->t->ns[from]) &&
        r <= acceptorState[from]->lastJoinRound
      )
    )
  )
  &&
  (forall p: Permission :: permVoteChannel->dom->val[p] ==> p is VotePerm &&
    (var r, n, voteResponse := p->r, p->n, permVoteChannel->val[p];
      Round(r) && Node(n) &&
      (
        var from := voteResponse->from;
        n == from &&
        voteInfo[r] is Some &&
        voteInfo[r]->t->ns[from]
      )
    )
  )
  &&
  (forall n: Node :: Node(n) ==>
    (
      var lastJoinRound, lastVoteRound, lastVoteValue := acceptorState[n]->lastJoinRound, acceptorState[n]->lastVoteRound, acceptorState[n]->lastVoteValue;
      lastVoteRound <= lastJoinRound &&
      (lastJoinRound == 0 || (Round(lastJoinRound) && joinedNodes[lastJoinRound][n])) &&
      (forall r: Round :: lastJoinRound < r && Round(r) ==> !joinedNodes[r][n]) &&
      (lastVoteRound == 0 || (Round(lastVoteRound) && voteInfo[lastVoteRound] is Some && voteInfo[lastVoteRound]->t->ns[n] && voteInfo[lastVoteRound]->t->value == lastVoteValue)) &&
      (forall r: Round :: lastVoteRound < r && Round(r) && voteInfo[r] is Some ==> !voteInfo[r]->t->ns[n])
    )
  )
}

function InvChannels (joinChannel: [Round][JoinResponse]int, permJoinChannel: JoinResponseChannel,
                      voteChannel: [Round][VoteResponse]int, permVoteChannel: VoteResponseChannel) : bool
{
  (forall r: Round, jr: JoinResponse :: 0 <= joinChannel[r][jr] && joinChannel[r][jr] <= 1) &&
  (forall r: Round, vr: VoteResponse :: 0 <= voteChannel[r][vr] && voteChannel[r][vr] <= 1) &&
  (forall r: Round, jr: JoinResponse ::
    joinChannel[r][jr] > 0 ==>
      permJoinChannel->dom->val[JoinPerm(r, jr->from)] &&
      permJoinChannel->val[JoinPerm(r, jr->from)] == jr) &&
  (forall r: Round, vr: VoteResponse ::
    voteChannel[r][vr] > 0 ==>
      permVoteChannel->dom->val[VotePerm(r, vr->from)] &&
      permVoteChannel->val[VotePerm(r, vr->from)] == vr)
}

yield invariant {:layer 1} YieldInit({:linear} ps: Set Permission);
invariant Init(ps, decision);
invariant InitLow(acceptorState, joinChannel, voteChannel, permJoinChannel, permVoteChannel);

yield invariant {:layer 1} YieldInv();
invariant Inv(joinedNodes, voteInfo, acceptorState, permJoinChannel, permVoteChannel);

yield invariant {:layer 1} YieldInvChannels();
invariant InvChannels(joinChannel, permJoinChannel, voteChannel, permVoteChannel);

////////////////////////////////////////////////////////////////////////////////

yield procedure {:layer 1}
Paxos({:layer 1}{:linear_in} ps: Set Permission)
refines A_Paxos;
requires call YieldInit(ps);
{
  var r: int;
  var {:layer 1}{:linear} r_lin: Set Permission;
  var {:layer 1}{:linear} ps': Set Permission;
  var {:layer 1}{:pending_async} PAs:[A_StartRound]int;

  call {:layer 1} joinedNodes := Copy((lambda r: Round:: NoNodes()));
  call {:layer 1} voteInfo := Copy((lambda r: Round:: None()));
  call {:layer 1} decision := Copy((lambda r: Round :: None()));
  r := 0;
  ps' := ps;
  while (*)
  invariant {:layer 1} 0 <= r;
  invariant {:layer 1} (forall r': Round :: r < r' ==> Set_IsSubset(AllPermissions(r'), ps'));
  invariant {:layer 1} PAs == ToMultiset((lambda pa: A_StartRound :: AllPermissions(pa->r) == pa->r_lin && Round(pa->r) && pa->r <= r));
  {
    r := r + 1;
    call {:layer 1} ps', r_lin := ExtractRoundPermission(ps', r);
    async call StartRound(r, r_lin);
  }
}

yield procedure {:layer 1}
StartRound(r: Round, {:layer 1}{:linear_in} r_lin: Set Permission)
refines A_StartRound;
requires {:layer 1} Round(r) && r_lin == AllPermissions(r);
requires call YieldInv();
requires call YieldInvChannels();
{
  var n: int;
  var {:layer 1}{:linear} p: One Permission;
  var {:layer 1}{:linear} ps: Set Permission;
  var {:layer 1}{:linear} ps': Set Permission;
  var {:layer 1}{:pending_async} PAs:[A_Join]int;

  call {:layer 1} ps, ps' := SplitPermissions(r, r_lin);
  n := 1;
  while (n <= numNodes)
  invariant {:layer 1} 1 <= n && n <= numNodes+1;
  invariant {:layer 1} (forall n': Node :: n <= n' && n' <= numNodes ==> ps->val[JoinPerm(r, n')]);
  invariant {:layer 1} PAs == ToMultiset((lambda pa: A_Join :: pa->r == r && 1 <= pa->n && pa->n < n && pa->p == One(JoinPerm(pa->r, pa->n))));
  {
    call {:layer 1} ps, p := ExtractJoinPermission(ps, r, n);
    async call Join(r, n, p);
    n := n + 1;
  }
  async call Propose(r, ps');
}

yield right procedure {:layer 1} ProposeHelper(r: Round) returns (maxRound: Round, maxValue: Value, {:layer 1} ns: NodeSet)
modifies permJoinChannel, joinChannel;
requires {:layer 1} Round(r);
requires {:layer 1} Inv(joinedNodes, voteInfo, acceptorState, permJoinChannel, permVoteChannel);
requires {:layer 1} InvChannels(joinChannel, permJoinChannel, voteChannel, permVoteChannel);
ensures {:layer 1} maxRound == MaxRound(r, ns, voteInfo);
ensures {:layer 1} Round(maxRound) ==> maxValue == voteInfo[maxRound]->t->value;
ensures {:layer 1} IsSubset(ns, joinedNodes[r]) && IsQuorum(ns);
ensures {:layer 1} Inv(joinedNodes, voteInfo, acceptorState, permJoinChannel, permVoteChannel);
ensures {:layer 1} InvChannels(joinChannel, permJoinChannel, voteChannel, permVoteChannel);
{
  var count: int;
  var joinResponse: JoinResponse;
  var {:layer 1}{:linear} receivedPermissions: Set Permission;
  var {:layer 1}{:linear} receivedPermission: One Permission;

  call {:layer 1} ns := Copy(NoNodes());
  call {:layer 1} receivedPermissions := InitializePermissions();
  count := 0;
  maxRound := 0;
  while (true)
  invariant {:layer 1} count == Cardinality(ns);
  invariant {:layer 1} (forall x: Node :: ns[x] ==> Node(x));
  invariant {:layer 1} IsSubset(ns, joinedNodes[r]);
  invariant {:layer 1} receivedPermissions->val == (lambda x: Permission :: x is JoinPerm && x->r == r && ns[x->n]);
  invariant {:layer 1} maxRound == MaxRound(r, ns, voteInfo);
  invariant {:layer 1} Round(maxRound) ==> maxValue == voteInfo[maxRound]->t->value;
  invariant {:layer 1} Inv(joinedNodes, voteInfo, acceptorState, permJoinChannel, permVoteChannel);
  invariant {:layer 1} InvChannels(joinChannel, permJoinChannel, voteChannel, permVoteChannel);
  {
    call joinResponse := ReceiveJoinResponse(r);
    call {:layer 1} receivedPermission, permJoinChannel := ReceiveJoinResponseIntro(r, joinResponse, permJoinChannel);
    call {:layer 1} MaxRoundLemma(voteInfo, r, ns, SingletonNode(receivedPermission->val->n));
    call {:layer 1} ns := AddToQuorum(ns, receivedPermission->val->n);
    call {:layer 1} receivedPermissions := AddPermission(receivedPermissions, receivedPermission);
    count := count + 1;
    if (joinResponse->lastVoteRound > maxRound) {
      maxRound := joinResponse->lastVoteRound;
      maxValue := joinResponse->lastVoteValue;
    }
    if (2 * count > numNodes) {
      break;
    }
  }
}

yield procedure {:layer 1}
Propose(r: Round, {:layer 1}{:linear_in} ps: Set Permission)
refines A_Propose;
requires {:layer 1} Round(r) && ps == ProposePermissions(r);
requires call YieldInv();
requires call YieldInvChannels();
{
  var {:layer 1} maxRound: Round;
  var maxValue: Value;
  var {:layer 1} ns: NodeSet;
  var n: int;
  var {:layer 1}{:linear} ps': Set Permission;
  var {:layer 1}{:linear} p: One Permission;
  var {:layer 1}{:linear} cp: One Permission;
  var {:layer 1}{:pending_async} PAs:[A_Vote]int;

  call maxRound, maxValue, ns := ProposeHelper(r);
  assume {:add_to_pool "NodeSet", ns} {:add_to_pool "MaxValue", maxValue} true;
  call {:layer 1} ps', cp := SplitConcludePermission(r, ps);
  n := 1;
  while (n <= numNodes)
  invariant {:layer 1} 1 <= n && n <= numNodes+1;
  invariant {:layer 1} (forall n': Node :: n <= n' && n' <= numNodes ==> ps'->val[VotePerm(r, n')]);
  invariant {:layer 1} PAs == ToMultiset((lambda pa: A_Vote :: pa->r == r && 1 <= pa->n && pa->n < n && pa->v == maxValue && pa->p->val == VotePerm(pa->r, pa->n)));
  {
    call {:layer 1} ps', p := ExtractVotePermission(ps', r, n);
    async call Vote(r, n, maxValue, p);
    n := n + 1;
  }
  async call Conclude(r, maxValue, cp);
  call {:layer 1} voteInfo := Copy(voteInfo[r := Some(VoteInfo(maxValue, NoNodes()))]);
}

yield procedure {:layer 1}
Conclude(r: Round, v: Value, {:layer 1}{:linear_in} p: One Permission)
refines A_Conclude;
requires {:layer 1} Round(r) && p->val == ConcludePerm(r);
requires call YieldInv();
requires call YieldInvChannels();
{
  var count: int;
  var voteResponse: VoteResponse;
  var {:layer 1} q: NodeSet;
  var {:linear} {:layer 1} receivedPermissions: Set Permission;
  var {:linear} {:layer 1} receivedPermission: One Permission;

  call {:layer 1} q := Copy(NoNodes());
  call {:layer 1} receivedPermissions := InitializePermissions();
  count := 0;
  while (true)
  invariant {:layer 1} count == Cardinality(q);
  invariant {:layer 1} (forall x: Node :: q[x] ==> Node(x));
  invariant {:layer 1} IsSubset(q, voteInfo[r]->t->ns);
  invariant {:layer 1} receivedPermissions->val == (lambda x: Permission :: x is VotePerm && x->r == r && q[x->n]);
  invariant {:layer 1} Inv(joinedNodes, voteInfo, acceptorState, permJoinChannel, permVoteChannel);
  invariant {:layer 1} InvChannels(joinChannel, permJoinChannel, voteChannel, permVoteChannel);
  {
    call voteResponse := ReceiveVoteResponse(r);
    call {:layer 1} receivedPermission, permVoteChannel := ReceiveVoteResponseIntro(r, voteResponse, permVoteChannel);
    call {:layer 1} q := AddToQuorum(q, receivedPermission->val->n);
    call {:layer 1} receivedPermissions := AddPermission(receivedPermissions, receivedPermission);
    count := count + 1;
    if (2 * count > numNodes) {
      call {:layer 1} decision := Copy(decision[r := Some(v)]);
      assume {:add_to_pool "NodeSet", q} true;
      break;
    }
  }
}

yield procedure {:layer 1}
Join(r: Round, n: Node, {:layer 1}{:linear_in} p: One Permission)
refines A_Join;
requires {:layer 1} Round(r) && Node(n) && p->val == JoinPerm(r, n);
requires call YieldInv();
{
  var doJoin: bool;
  var lastVoteRound: Round;
  var lastVoteValue: Value;

  call doJoin, lastVoteRound, lastVoteValue := JoinUpdate(r, n);
  if (doJoin) {
    call SendJoinResponse(r, n, lastVoteRound, lastVoteValue);
    call {:layer 1} permJoinChannel := SendJoinResponseIntro(JoinResponse(n, lastVoteRound, lastVoteValue), p, permJoinChannel);
    call {:layer 1} joinedNodes := Copy(joinedNodes[r := joinedNodes[r][n := true]]);
  }
}

yield procedure {:layer 1}
Vote(r: Round, n: Node, v: Value, {:layer 1}{:linear_in} p: One Permission)
refines A_Vote;
requires {:layer 1} Round(r) && Node(n) && p->val == VotePerm(r, n);
requires call YieldInv();
{
  var doVote:bool;

  call doVote := VoteUpdate(r, n, v);
  if (doVote) {
    call SendVoteResponse(r, n);
    call {:layer 1} permVoteChannel := SendVoteResponseIntro(VoteResponse(n), p, permVoteChannel);
    call {:layer 1} joinedNodes := Copy(joinedNodes[r := joinedNodes[r][n := true]]);
    call {:layer 1} voteInfo := Copy(voteInfo[r := Some(VoteInfo(voteInfo[r]->t->value, voteInfo[r]->t->ns[n := true]))]);
  }
}

////////////////////////////////////////////////////////////////////////////////

// Trusted lemmas for the proof of Propose and Conclude
pure procedure AddToQuorum(q: NodeSet, n: Node) returns (q': NodeSet);
requires !q[n];
ensures q' == q[n := true];
ensures Cardinality(q') == Cardinality(q) + 1;

pure procedure MaxRoundLemma(voteInfo:[Round]Option VoteInfo, r: Round, ns1: NodeSet, ns2: NodeSet);
requires Round(r);
ensures MaxRound(r, MapOr(ns1, ns2), voteInfo) ==
         if (MaxRound(r, ns1, voteInfo) < MaxRound(r, ns2, voteInfo))
         then MaxRound(r, ns2, voteInfo)
         else MaxRound(r, ns1, voteInfo);

////////////////////////////////////////////////////////////////////////////////

atomic action {:layer 1} A_JoinUpdate(r: Round, n: Node)
returns (join:bool, lastVoteRound: Round, lastVoteValue: Value)
modifies acceptorState;
{
  var lastJoinRound: Round;
  lastJoinRound := acceptorState[n]->lastJoinRound;
  if (r > lastJoinRound) {
    lastVoteRound := acceptorState[n]->lastVoteRound;
    lastVoteValue := acceptorState[n]->lastVoteValue;
    acceptorState[n] := AcceptorState(r, lastVoteRound, lastVoteValue);
    join := true;
  } else {
    join := false;
  }
}

atomic action {:layer 1} A_VoteUpdate(r: Round, n: Node, v: Value)
returns (vote:bool)
modifies acceptorState;
{
  var lastJoinRound: Round;
  lastJoinRound := acceptorState[n]->lastJoinRound;
  if (r >= lastJoinRound) {
    acceptorState[n] := AcceptorState(r, r, v);
    vote := true;
  } else {
    vote := false;
  }
}

yield procedure {:layer 0} JoinUpdate(r: Round, n: Node) returns (join:bool, lastVoteRound: Round, lastVoteValue: Value);
refines A_JoinUpdate;

yield procedure {:layer 0} VoteUpdate(r: Round, n: Node, v: Value) returns (vote:bool);
refines A_VoteUpdate;

//// Channel send/receive actions

left action {:layer 1} A_SendJoinResponse(round: Round, from: Node, lastVoteRound: Round, lastVoteValue: Value)
modifies joinChannel;
{
  joinChannel[round][JoinResponse(from, lastVoteRound, lastVoteValue)] := joinChannel[round][JoinResponse(from, lastVoteRound, lastVoteValue)] + 1;
}

right action {:layer 1} A_ReceiveJoinResponse(round: Round)
returns (joinResponse: JoinResponse)
modifies joinChannel;
{
  assume joinChannel[round][joinResponse] > 0;
  joinChannel[round][joinResponse] := joinChannel[round][joinResponse] - 1;
}

left action {:layer 1} A_SendVoteResponse(round: Round, from: Node)
modifies voteChannel;
{
  voteChannel[round][VoteResponse(from)] := voteChannel[round][VoteResponse(from)] + 1;
}

right action {:layer 1} A_ReceiveVoteResponse(round: Round)
returns (voteResponse: VoteResponse)
modifies voteChannel;
{
  assume voteChannel[round][voteResponse] > 0;
  voteChannel[round][voteResponse] := voteChannel[round][voteResponse] - 1;
}

yield procedure {:layer 0}
SendJoinResponse(round: Round, from: Node, lastVoteRound: Round, lastVoteValue: Value);
refines A_SendJoinResponse;

yield procedure {:layer 0}
ReceiveJoinResponse(round: Round) returns (joinResponse: JoinResponse);
refines A_ReceiveJoinResponse;

yield procedure {:layer 0}
SendVoteResponse(round: Round, from: Node);
refines A_SendVoteResponse;

yield procedure {:layer 0}
ReceiveVoteResponse(round: Round) returns (voteResponse: VoteResponse);
refines A_ReceiveVoteResponse;

//// Introduction procedures to make send/receive more abstract

pure action SendJoinResponseIntro(joinResponse: JoinResponse, {:linear_in} p: One Permission, {:linear_in} permJoinChannel: JoinResponseChannel)
returns ({:linear} permJoinChannel': JoinResponseChannel)
{
  permJoinChannel' := permJoinChannel;
  call Map_Put(permJoinChannel', p, joinResponse);
}

pure action ReceiveJoinResponseIntro(round: Round, joinResponse: JoinResponse, {:linear_in} permJoinChannel: JoinResponseChannel)
returns ({:linear} receivedPermission: One Permission, {:linear} permJoinChannel': JoinResponseChannel)
{
  var x: JoinResponse;
  permJoinChannel' := permJoinChannel;
  call receivedPermission, x := Map_Get(permJoinChannel', JoinPerm(round, joinResponse->from));
}

pure action SendVoteResponseIntro(voteResponse: VoteResponse, {:linear_in} p: One Permission, {:linear_in} permVoteChannel: VoteResponseChannel)
returns ({:linear} permVoteChannel': VoteResponseChannel)
{
  permVoteChannel' := permVoteChannel;
  call Map_Put(permVoteChannel', p, voteResponse);
}

pure action ReceiveVoteResponseIntro(round: Round, voteResponse: VoteResponse, {:linear_in} permVoteChannel: VoteResponseChannel)
returns ({:linear} receivedPermission: One Permission, {:linear} permVoteChannel': VoteResponseChannel)
{
  var x: VoteResponse;
  permVoteChannel' := permVoteChannel;
  call receivedPermission, x := Map_Get(permVoteChannel', VotePerm(round, voteResponse->from));
}

//// Permission accounting

pure action ExtractRoundPermission({:linear_in} ps: Set Permission, r: Round)
returns ({:linear} ps': Set Permission, {:linear} r_lin: Set Permission)
{
  ps' := ps;
  r_lin := AllPermissions(r);
  call Set_Split(ps', r_lin);
}

pure action SplitPermissions(r: Round, {:linear_in} r_lin: Set Permission)
returns ({:linear} ps: Set Permission, {:linear} ps': Set Permission)
{
  ps' := r_lin;
  call ps := Set_Get(ps', JoinPermissions(r));
  assert ps' == ProposePermissions(r);
}

pure action ExtractJoinPermission({:linear_in} ps: Set Permission, r: Round, n: Node)
returns ({:linear} ps': Set Permission, {:linear} p: One Permission)
{
  ps' := ps;
  call p := One_Get(ps', JoinPerm(r, n));
}

pure action SplitConcludePermission(r: Round, {:linear_in} ps: Set Permission)
returns ({:linear} ps': Set Permission, {:linear} cp: One Permission)
{
  ps' := ps;
  call cp := One_Get(ps', ConcludePerm(r));
}

pure action ExtractVotePermission({:linear_in} ps: Set Permission, r: Round, n: Node)
returns ({:linear} ps': Set Permission, {:linear} p: One Permission)
{
  ps' := ps;
  call p := One_Get(ps', VotePerm(r, n));
}

pure action InitializePermissions()
returns ({:linear} receivedPermissions: Set Permission)
{
  call receivedPermissions := Set_MakeEmpty();
}

pure action AddPermission({:linear_in} receivedPermissions: Set Permission, {:linear_in} p: One Permission)
returns ({:linear}receivedPermissions': Set Permission)
{
  receivedPermissions' := receivedPermissions;
  call One_Put(receivedPermissions', p);
}

// Local Variables:
// flycheck-disabled-checkers: (boogie)
// End:
