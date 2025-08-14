function {:inline} Inv (joinedNodes: [Round]NodeSet, voteInfo: [Round]Option VoteInfo, acceptorState: [Node]AcceptorState,
              joinChannel: [Round][JoinResponse]int, joinChannelPermissions: Set Permission,
              voteChannel: [Round][VoteResponse]int, voteChannelPermissions: Set Permission) : bool
{
  (forall r: Round, jr: JoinResponse :: 0 <= joinChannel[r][jr] && joinChannel[r][jr] <= 1)
  &&
  (forall r: Round, jr1: JoinResponse, jr2: JoinResponse :: jr1->from == jr2->from && joinChannel[r][jr1] > 0 && joinChannel[r][jr2] > 0 ==> jr1 == jr2)
  &&
  (forall r: Round, jr: JoinResponse :: joinChannel[r][jr] > 0 ==> Round(r) && Node(jr->from) && Set_Contains(joinChannelPermissions, JoinPerm(r, jr->from)) &&
    (jr is JoinAccept ==>
      (
        var from, maxRound, maxValue := jr->from, jr->lastVoteRound, jr->lastVoteValue;
        joinedNodes[r][from] &&
        0 <= maxRound && maxRound < r &&
        (maxRound == 0 || (voteInfo[maxRound] is Some && voteInfo[maxRound]->t->ns[from] && voteInfo[maxRound]->t->value == maxValue)) &&
        (forall r': Round :: maxRound < r' && r' < r && voteInfo[r'] is Some ==> !voteInfo[r']->t->ns[from]) &&
        r <= acceptorState[from]->lastJoinRound
      )
    )
  )

  &&
  (forall r: Round, vr: VoteResponse :: voteChannel[r][vr] > 0 ==> Round(r) && Node(vr->from) && Set_Contains(voteChannelPermissions, VotePerm(r, vr->from)) &&
    (vr is VoteAccept ==> voteInfo[r] is Some && voteInfo[r]->t->ns[vr->from])
  )
  &&
  (forall r: Round, vr: VoteResponse :: 0 <= voteChannel[r][vr] && voteChannel[r][vr] <= 1)
  &&
  (forall r: Round, vr1: VoteResponse, vr2: VoteResponse :: vr1->from == vr2->from && voteChannel[r][vr1] > 0 && voteChannel[r][vr2] > 0 ==> vr1 == vr2)

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

yield invariant {:layer 1} YieldInit({:linear} ps: Set Permission);
preserves Init(ps, decision);
preserves InitLow(acceptorState, joinChannel, voteChannel, joinChannelPermissions, voteChannelPermissions);

yield invariant {:layer 1} YieldInv();
preserves Inv(joinedNodes, voteInfo, acceptorState, joinChannel, joinChannelPermissions, voteChannel, voteChannelPermissions);

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
{
  var n: int;
  var {:layer 1}{:linear} p: One Permission;
  var {:layer 1}{:linear} ps: Set Permission;
  var {:layer 1}{:linear} ps': Set Permission;
  var {:layer 1}{:pending_async} PAs:[A_Join]int;

  assert {:layer 1} Set_Difference(AllPermissions(r), JoinPermissions(r)) == ProposePermissions(r);
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

yield procedure {:layer 1}
Join(r: Round, n: Node, {:layer 1}{:linear_in} p: One Permission)
refines A_Join;
requires {:layer 1} Round(r) && Node(n) && p->val == JoinPerm(r, n);
requires call YieldInv();
{
  var joinResponse: JoinResponse;

  call joinResponse := JoinUpdate(r, n);
  call SendJoinResponse(r, joinResponse);
  if (joinResponse is JoinAccept) {
    call {:layer 1} joinedNodes := Copy(joinedNodes[r := joinedNodes[r][n := true]]);
  }
  call {:layer 1} One_Put(joinChannelPermissions, p);
}

yield right procedure {:layer 1} ProposeHelper(r: Round) returns (maxRound: Round, maxValue: Value, count: int, {:layer 1} ns: NodeSet)
modifies joinChannelPermissions, joinChannel;
requires {:layer 1} Round(r);
requires {:layer 1} Inv(joinedNodes, voteInfo, acceptorState, joinChannel, joinChannelPermissions, voteChannel, voteChannelPermissions);
ensures {:layer 1} maxRound == MaxRound(r, ns, voteInfo);
ensures {:layer 1} Round(maxRound) ==> maxValue == voteInfo[maxRound]->t->value;
ensures {:layer 1} count == Cardinality(ns);
ensures {:layer 1} (forall x: Node :: ns[x] ==> Node(x));
ensures {:layer 1} IsSubset(ns, joinedNodes[r]);
ensures {:layer 1} Inv(joinedNodes, voteInfo, acceptorState, joinChannel, joinChannelPermissions, voteChannel, voteChannelPermissions);
{
  var n: int;
  var joinResponse: JoinResponse;
  var {:layer 1}{:linear} receivedPermission: One Permission;

  call {:layer 1} ns := Copy(NoNodes());
  n := 0;
  count := 0;
  maxRound := 0;
  while (n < numNodes)
  invariant {:layer 1} 0 <= n && n <= numNodes;
  invariant {:layer 1} count == Cardinality(ns);
  invariant {:layer 1} (forall x: Node :: ns[x] ==> Node(x) && usedPermissions->val[JoinPerm(r, x)]);
  invariant {:layer 1} IsSubset(ns, joinedNodes[r]);
  invariant {:layer 1} maxRound == MaxRound(r, ns, voteInfo);
  invariant {:layer 1} Round(maxRound) ==> maxValue == voteInfo[maxRound]->t->value;
  invariant {:layer 1} Inv(joinedNodes, voteInfo, acceptorState, joinChannel, joinChannelPermissions, voteChannel, voteChannelPermissions);
  {
    call joinResponse := ReceiveJoinResponse(r);
    call {:layer 1} joinChannelPermissions, usedPermissions := MovePermission(JoinPerm(r, joinResponse->from), joinChannelPermissions, usedPermissions);
    if (joinResponse is JoinAccept) {
      //assume {:add_to_pool "Permission", JoinPerm(r, joinResponse->from)} true;
      call {:layer 1} MaxRoundLemma(voteInfo, r, ns, SingletonNode(joinResponse->from));
      call {:layer 1} ns := AddToQuorum(ns, joinResponse->from);
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
}

yield procedure {:layer 1}
Propose(r: Round, {:layer 1}{:linear_in} ps: Set Permission)
refines A_Propose;
requires {:layer 1} Round(r) && ps == ProposePermissions(r);
requires call YieldInv();
{
  var {:layer 1} maxRound: Round;
  var maxValue: Value;
  var {:layer 1} ns: NodeSet;
  var n, count: int;
  var {:layer 1}{:linear} ps': Set Permission;
  var {:layer 1}{:linear} p: One Permission;
  var {:layer 1}{:linear} cp: One Permission;
  var {:layer 1}{:pending_async} PAs:[A_Vote]int;

  call maxRound, maxValue, count, ns := ProposeHelper(r);
  call {:layer 1} ps', cp := SplitConcludePermission(r, ps);
  if (2 * count > numNodes) {
    assume {:add_to_pool "NodeSet", ns} {:add_to_pool "MaxValue", maxValue} true;
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
  } else {
    call {:layer 1} Set_Put(usedPermissions, ps');
  }
}

yield procedure {:layer 1}
Vote(r: Round, n: Node, v: Value, {:layer 1}{:linear_in} p: One Permission)
refines A_Vote;
requires {:layer 1} Round(r) && Node(n) && p->val == VotePerm(r, n);
requires call YieldInv();
{
  var voteResponse: VoteResponse;

  call voteResponse := VoteUpdate(r, n, v);
  call SendVoteResponse(r, voteResponse);
  if (voteResponse is VoteAccept) {
    call {:layer 1} joinedNodes := Copy(joinedNodes[r := joinedNodes[r][n := true]]);
    call {:layer 1} voteInfo := Copy(voteInfo[r := Some(VoteInfo(voteInfo[r]->t->value, voteInfo[r]->t->ns[n := true]))]);
  }
  call {:layer 1} One_Put(voteChannelPermissions, p);
}

yield procedure {:layer 1}
Conclude(r: Round, v: Value, {:layer 1}{:linear_in} p: One Permission)
refines A_Conclude;
requires {:layer 1} Round(r) && p->val == ConcludePerm(r);
requires call YieldInv();
{
  var n, count: int;
  var voteResponse: VoteResponse;
  var {:layer 1} q: NodeSet;
  var {:linear} {:layer 1} receivedPermission: One Permission;

  call {:layer 1} q := Copy(NoNodes());
  n := 0;
  count := 0;
  while (n < numNodes)
  invariant {:layer 1} 0 <= n && n <= numNodes;
  invariant {:layer 1} count == Cardinality(q);
  invariant {:layer 1} (forall x: Node :: q[x] ==> Node(x) && usedPermissions->val[VotePerm(r, x)]);
  invariant {:layer 1} IsSubset(q, voteInfo[r]->t->ns);
  invariant {:layer 1} Inv(joinedNodes, voteInfo, acceptorState, joinChannel, joinChannelPermissions, voteChannel, voteChannelPermissions);
  {
    call voteResponse := ReceiveVoteResponse(r);
    call {:layer 1} voteChannelPermissions, usedPermissions := MovePermission(VotePerm(r, voteResponse->from), voteChannelPermissions, usedPermissions);
    if (voteResponse is VoteAccept) {
      call {:layer 1} q := AddToQuorum(q, voteResponse->from);
      count := count + 1;
      if (2 * count > numNodes) {
        call {:layer 1} decision := Copy(decision[r := Some(v)]);
        assume {:add_to_pool "NodeSet", q} true;
        break;
      }
    }
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

yield procedure {:layer 0} JoinUpdate(r: Round, n: Node) returns (joinResponse: JoinResponse);
refines atomic action {:layer 1} _
{
  var lastJoinRound: Round;
  var lastVoteRound: Round;
  var lastVoteValue: Value;

  lastJoinRound := acceptorState[n]->lastJoinRound;
  if (r > lastJoinRound) {
    lastVoteRound := acceptorState[n]->lastVoteRound;
    lastVoteValue := acceptorState[n]->lastVoteValue;
    acceptorState[n] := AcceptorState(r, lastVoteRound, lastVoteValue);
    joinResponse := JoinAccept(n, lastVoteRound, lastVoteValue);
  } else {
    joinResponse := JoinReject(n);
  }
}

yield procedure {:layer 0} VoteUpdate(r: Round, n: Node, v: Value) returns (voteResponse: VoteResponse);
refines atomic action {:layer 1} _
{
  var lastJoinRound: Round;

  lastJoinRound := acceptorState[n]->lastJoinRound;
  if (r >= lastJoinRound) {
    acceptorState[n] := AcceptorState(r, r, v);
    voteResponse := VoteAccept(n);
  } else {
    voteResponse := VoteReject(n);
  }
}

//// Channel send/receive actions

yield procedure {:layer 0} SendJoinResponse(round: Round, joinResponse: JoinResponse);
refines left action {:layer 1} _
{
  joinChannel[round][joinResponse] := joinChannel[round][joinResponse] + 1;
}

yield procedure {:layer 0} ReceiveJoinResponse(round: Round) returns (joinResponse: JoinResponse);
refines right action {:layer 1} _
{
  assume joinChannel[round][joinResponse] > 0;
  joinChannel[round][joinResponse] := joinChannel[round][joinResponse] - 1;
}

yield procedure {:layer 0} SendVoteResponse(round: Round, voteResponse: VoteResponse);
refines left action {:layer 1} _
{
  voteChannel[round][voteResponse] := voteChannel[round][voteResponse] + 1;
}

yield procedure {:layer 0} ReceiveVoteResponse(round: Round) returns (voteResponse: VoteResponse);
refines right action {:layer 1} _
{
  assume voteChannel[round][voteResponse] > 0;
  voteChannel[round][voteResponse] := voteChannel[round][voteResponse] - 1;
}

//// Permission accounting

pure action MovePermission(p: Permission, {:linear_in} from: Set Permission, {:linear_in} to: Set Permission)
returns ({:linear} from': Set Permission, {:linear} to': Set Permission)
{
  var {:linear} one_p: One Permission;

  from' := from;
  to' := to;
  call one_p := One_Get(from', p);
  call One_Put(to', one_p);
}

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
  ps := JoinPermissions(r);
  call Set_Split(ps', ps);
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

// Local Variables:
// flycheck-disabled-checkers: (boogie)
// End:
