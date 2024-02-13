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

yield invariant {:layer 1} YieldInit({:linear "perm"} rs: [Round]bool);
invariant Init(rs, decision);
invariant InitLow(acceptorState, joinChannel, voteChannel, permJoinChannel, permVoteChannel);

yield invariant {:layer 1} YieldInv();
invariant Inv(joinedNodes, voteInfo, acceptorState, permJoinChannel, permVoteChannel);

yield invariant {:layer 1} YieldInvChannels();
invariant InvChannels(joinChannel, permJoinChannel, voteChannel, permVoteChannel);

////////////////////////////////////////////////////////////////////////////////

yield procedure {:layer 1}
Paxos({:layer 1}{:linear_in "perm"} rs: [Round]bool)
refines A_Paxos;
requires call YieldInit(rs);
{
  var r: int;
  var {:layer 1}{:linear "perm"} r_lin: int;
  var {:layer 1}{:linear "perm"} rs': [Round]bool;
  var {:layer 1}{:pending_async} PAs:[A_StartRound]int;

  call {:layer 1} joinedNodes := Copy((lambda r: Round:: NoNodes()));
  call {:layer 1} voteInfo := Copy((lambda r: Round:: None()));
  call {:layer 1} decision := Copy((lambda r: Round :: None()));
  r := 0;
  rs' := rs;
  while (*)
  invariant {:layer 1} 0 <= r;
  invariant {:layer 1} (forall r': Round :: r < r' ==> rs'[r']);
  invariant {:layer 1} PAs == ToMultiset((lambda pa: A_StartRound :: pa->r == pa->r_lin && Round(pa->r) && pa->r <= r));
  {
    r := r + 1;
    call {:layer 1} rs', r_lin := ExtractRoundPermission(rs', r);
    async call StartRound(r, r_lin);
  }
}

yield procedure {:layer 1}
StartRound(r: Round, {:layer 1}{:linear_in "perm"} r_lin: Round)
refines A_StartRound;
requires {:layer 1} Round(r) && r_lin == r;
requires call YieldInv();
requires call YieldInvChannels();
{
  var n: int;
  var {:layer 1}{:linear "perm"} p: Permission;
  var {:layer 1}{:linear "perm"} ps: [Permission]bool;
  var {:layer 1}{:linear "perm"} ps': [Permission]bool;
  var {:layer 1}{:pending_async} PAs:[A_Join]int;

  call {:layer 1} ps, ps' := SplitPermissions(r_lin);
  n := 1;
  while (n <= numNodes)
  invariant {:layer 1} 1 <= n && n <= numNodes+1;
  invariant {:layer 1} (forall n': Node :: n <= n' && n' <= numNodes ==> ps[JoinPerm(r, n')]);
  invariant {:layer 1} PAs == ToMultiset((lambda pa: A_Join :: pa->r == r && 1 <= pa->n && pa->n < n && pa->p == JoinPerm(pa->r, pa->n)));
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
  var {:layer 1}{:linear "perm"} receivedPermissions: [Permission]bool;
  var {:layer 1}{:linear "perm"} receivedPermission: Permission;

  call {:layer 1} ns := Copy(NoNodes());
  call {:layer 1} receivedPermissions := InitializePermissions();
  count := 0;
  maxRound := 0;
  while (true)
  invariant {:layer 1} count == Cardinality(ns);
  invariant {:layer 1} (forall x: Node :: ns[x] ==> Node(x));
  invariant {:layer 1} IsSubset(ns, joinedNodes[r]);
  invariant {:layer 1} receivedPermissions == (lambda x: Permission :: x is JoinPerm && x->r == r && ns[x->n]);
  invariant {:layer 1} maxRound == MaxRound(r, ns, voteInfo);
  invariant {:layer 1} Round(maxRound) ==> maxValue == voteInfo[maxRound]->t->value;
  invariant {:layer 1} Inv(joinedNodes, voteInfo, acceptorState, permJoinChannel, permVoteChannel);
  invariant {:layer 1} InvChannels(joinChannel, permJoinChannel, voteChannel, permVoteChannel);
  {
    call joinResponse := ReceiveJoinResponse(r);
    call {:layer 1} receivedPermission, permJoinChannel := ReceiveJoinResponseIntro(r, joinResponse, permJoinChannel);
    call {:layer 1} MaxRoundLemma(voteInfo, r, ns, SingletonNode(receivedPermission->n));
    call {:layer 1} ns := AddToQuorum(ns, receivedPermission->n);
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
Propose(r: Round, {:layer 1}{:linear_in "perm"} ps: [Permission]bool)
refines A_Propose;
requires {:layer 1} Round(r) && ps == ProposePermissions(r);
requires call YieldInv();
requires call YieldInvChannels();
{
  var {:layer 1} maxRound: Round;
  var maxValue: Value;
  var {:layer 1} ns: NodeSet;
  var n: int;
  var {:layer 1}{:linear "perm"} ps': [Permission]bool;
  var {:layer 1}{:linear "perm"} p: Permission;
  var {:layer 1}{:linear "perm"} cp: Permission;
  var {:layer 1}{:pending_async} PAs:[A_Vote]int;

  call maxRound, maxValue, ns := ProposeHelper(r);
  assume {:add_to_pool "NodeSet", ns} {:add_to_pool "MaxValue", maxValue} true;
  call {:layer 1} ps', cp := SplitConcludePermission(r, ps);
  n := 1;
  while (n <= numNodes)
  invariant {:layer 1} 1 <= n && n <= numNodes+1;
  invariant {:layer 1} (forall n': Node :: n <= n' && n' <= numNodes ==> ps'[VotePerm(r, n')]);
  invariant {:layer 1} PAs == ToMultiset((lambda pa: A_Vote :: pa->r == r && 1 <= pa->n && pa->n < n && pa->v == maxValue && pa->p == VotePerm(pa->r, pa->n)));
  {
    call {:layer 1} ps', p := ExtractVotePermission(ps', r, n);
    async call Vote(r, n, maxValue, p);
    n := n + 1;
  }
  async call Conclude(r, maxValue, cp);
  call {:layer 1} voteInfo := Copy(voteInfo[r := Some(VoteInfo(maxValue, NoNodes()))]);
}

yield procedure {:layer 1}
Conclude(r: Round, v: Value, {:layer 1}{:linear_in "perm"} p: Permission)
refines A_Conclude;
requires {:layer 1} Round(r) && p == ConcludePerm(r);
requires call YieldInv();
requires call YieldInvChannels();
{
  var count: int;
  var voteResponse: VoteResponse;
  var {:layer 1} q: NodeSet;
  var {:linear "perm"} {:layer 1} receivedPermissions: [Permission]bool;
  var {:linear "perm"} {:layer 1} receivedPermission: Permission;

  call {:layer 1} q := Copy(NoNodes());
  call {:layer 1} receivedPermissions := InitializePermissions();
  count := 0;
  while (true)
  invariant {:layer 1} count == Cardinality(q);
  invariant {:layer 1} (forall x: Node :: q[x] ==> Node(x));
  invariant {:layer 1} IsSubset(q, voteInfo[r]->t->ns);
  invariant {:layer 1} receivedPermissions == (lambda x: Permission :: x is VotePerm && x->r == r && q[x->n]);
  invariant {:layer 1} Inv(joinedNodes, voteInfo, acceptorState, permJoinChannel, permVoteChannel);
  invariant {:layer 1} InvChannels(joinChannel, permJoinChannel, voteChannel, permVoteChannel);
  {
    call voteResponse := ReceiveVoteResponse(r);
    call {:layer 1} receivedPermission, permVoteChannel := ReceiveVoteResponseIntro(r, voteResponse, permVoteChannel);
    call {:layer 1} q := AddToQuorum(q, receivedPermission->n);
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
Join(r: Round, n: Node, {:layer 1}{:linear_in "perm"} p: Permission)
refines A_Join;
requires {:layer 1} Round(r) && Node(n) && p == JoinPerm(r, n);
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
Vote(r: Round, n: Node, v: Value, {:layer 1}{:linear_in "perm"} p: Permission)
refines A_Vote;
requires {:layer 1} Round(r) && Node(n) && p == VotePerm(r, n);
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

pure action SendJoinResponseIntro(joinResponse: JoinResponse, {:linear_in "perm"} p: Permission, {:linear_in "perm"} permJoinChannel: JoinResponseChannel)
returns ({:linear "perm"} permJoinChannel': JoinResponseChannel)
{
  permJoinChannel' := Map_Update(permJoinChannel, p, joinResponse);
}

pure action ReceiveJoinResponseIntro(round: Round, joinResponse: JoinResponse, {:linear_in "perm"} permJoinChannel: JoinResponseChannel)
returns ({:linear "perm"} receivedPermission: Permission, {:linear "perm"} permJoinChannel': JoinResponseChannel)
{
  assert permJoinChannel->dom->val[JoinPerm(round, joinResponse->from)];
  receivedPermission := JoinPerm(round, joinResponse->from);
  permJoinChannel' := Map_Remove(permJoinChannel, receivedPermission);
}

pure action SendVoteResponseIntro(voteResponse: VoteResponse, {:linear_in "perm"} p: Permission, {:linear_in "perm"} permVoteChannel: VoteResponseChannel)
returns ({:linear "perm"} permVoteChannel': VoteResponseChannel)
{
  permVoteChannel' := Map_Update(permVoteChannel, p, voteResponse);
}

pure action ReceiveVoteResponseIntro(round: Round, voteResponse: VoteResponse, {:linear_in "perm"} permVoteChannel: VoteResponseChannel)
returns ({:linear "perm"} receivedPermission: Permission, {:linear "perm"} permVoteChannel': VoteResponseChannel)
{
  assert permVoteChannel->dom->val[VotePerm(round, voteResponse->from)];
  receivedPermission := VotePerm(round, voteResponse->from);
  permVoteChannel' := Map_Remove(permVoteChannel, receivedPermission);
}

//// Permission accounting

pure action ExtractRoundPermission({:linear_in "perm"} rs: [Round]bool, r: Round)
returns ({:linear "perm"} rs': [Round]bool, {:linear "perm"} r_lin: Round)
{
  assert rs[r];
  rs', r_lin := rs[r := false], r;
}

pure action SplitPermissions({:linear_in "perm"} r_lin: Round)
returns ({:linear "perm"} ps: [Permission]bool, {:linear "perm"} ps': [Permission]bool)
{
  ps, ps' := JoinPermissions(r_lin), ProposePermissions(r_lin);
}

pure action ExtractJoinPermission({:linear_in "perm"} ps: [Permission]bool, r: Round, n: Node)
returns ({:linear "perm"} ps': [Permission]bool, {:linear "perm"} p: Permission)
{
  assert ps[JoinPerm(r, n)];
  p := JoinPerm(r, n);
  ps' := ps[p := false];
}

pure action SplitConcludePermission(r: Round, {:linear_in "perm"} ps: [Permission]bool)
returns ({:linear "perm"} ps': [Permission]bool, {:linear "perm"} cp: Permission)
{
  assert ps == ProposePermissions(r);
  ps', cp := VotePermissions(r), ConcludePerm(r);
}

pure action ExtractVotePermission({:linear_in "perm"} ps: [Permission]bool, r: Round, n: Node)
returns ({:linear "perm"} ps': [Permission]bool, {:linear "perm"} p: Permission)
{
  assert ps[VotePerm(r, n)];
  p := VotePerm(r, n);
  ps' := ps[p := false];
}

pure action InitializePermissions()
returns ({:linear "perm"} receivedPermissions: [Permission]bool)
{
  receivedPermissions := MapConst(false);
}

pure action AddPermission({:linear_in "perm"} receivedPermissions: [Permission]bool, {:linear_in "perm"} p: Permission)
returns ({:linear "perm"}receivedPermissions': [Permission]bool)
{
  receivedPermissions' := receivedPermissions[p := true];
}

// Local Variables:
// flycheck-disabled-checkers: (boogie)
// End:
