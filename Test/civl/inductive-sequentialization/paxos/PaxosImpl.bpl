procedure {:atomic}{:layer 2} A_Paxos({:linear_in "perm"} rs: [Round]bool)
returns ({:pending_async "A_StartRound"} PAs:[PA]int)
modifies pendingAsyncs;
{
  var numRounds: int;
  assert Init(rs, joinedNodes, voteInfo, decision, pendingAsyncs);
  assert triggerRound(0);
  assume 0 <= numRounds;
  assume triggerRound(numRounds);
  PAs := (lambda pa: PA :: if is#A_StartRound(pa) && round#A_StartRound(pa) == round_lin#A_StartRound(pa) && Round(round#A_StartRound(pa)) && round#A_StartRound(pa) <= numRounds then 1 else 0);
  pendingAsyncs := PAs;
}

////////////////////////////////////////////////////////////////////////////////

function Inv (joinedNodes: [Round]NodeSet, voteInfo: [Round]Option VoteInfo, acceptorState: [Node]AcceptorState,
              permJoinChannel: JoinResponseChannel, permVoteChannel: VoteResponseChannel) : bool
{
  (forall p: Permission :: domain#JoinResponseChannel(permJoinChannel)[p] ==> is#JoinPerm(p) &&
    (var r, n, joinResponse := r#JoinPerm(p), n#JoinPerm(p), contents#JoinResponseChannel(permJoinChannel)[p];
      Round(r) && Node(n) &&
      (
        var from, maxRound, maxValue := from#JoinResponse(joinResponse), lastVoteRound#JoinResponse(joinResponse), lastVoteValue#JoinResponse(joinResponse);
        n == from &&
        joinedNodes[r][from] &&
        0 <= maxRound && maxRound < r &&
        (maxRound == 0 || (is#Some(voteInfo[maxRound]) && ns#VoteInfo(t#Some(voteInfo[maxRound]))[from] && value#VoteInfo(t#Some(voteInfo[maxRound])) == maxValue)) &&
        (forall r': Round :: maxRound < r' && r' < r && is#Some(voteInfo[r']) ==> !ns#VoteInfo(t#Some(voteInfo[r']))[from]) &&
        r <= lastJoinRound#AcceptorState(acceptorState[from])
      )
    )
  )
  &&
  (forall p: Permission :: domain#VoteResponseChannel(permVoteChannel)[p] ==> is#VotePerm(p) &&
    (var r, n, voteResponse := r#VotePerm(p), n#VotePerm(p), contents#VoteResponseChannel(permVoteChannel)[p];
      Round(r) && Node(n) &&
      (
        var from := from#VoteResponse(voteResponse);
        n == from &&
        is#Some(voteInfo[r]) &&
        ns#VoteInfo(t#Some(voteInfo[r]))[from]
      )
    )
  )
  &&
  (forall n: Node :: Node(n) ==>
    (
      var lastJoinRound, lastVoteRound, lastVoteValue := lastJoinRound#AcceptorState(acceptorState[n]), lastVoteRound#AcceptorState(acceptorState[n]), lastVoteValue#AcceptorState(acceptorState[n]);
      lastVoteRound <= lastJoinRound &&
      (lastJoinRound == 0 || (Round(lastJoinRound) && joinedNodes[lastJoinRound][n])) &&
      (forall r: Round :: lastJoinRound < r && Round(r) ==> !joinedNodes[r][n]) &&
      (lastVoteRound == 0 || (Round(lastVoteRound) && is#Some(voteInfo[lastVoteRound]) && ns#VoteInfo(t#Some(voteInfo[lastVoteRound]))[n] && value#VoteInfo(t#Some(voteInfo[lastVoteRound])) == lastVoteValue)) &&
      (forall r: Round :: lastVoteRound < r && Round(r) && is#Some(voteInfo[r]) ==> !ns#VoteInfo(t#Some(voteInfo[r]))[n])
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
      domain#JoinResponseChannel(permJoinChannel)[JoinPerm(r, from#JoinResponse(jr))] &&
      contents#JoinResponseChannel(permJoinChannel)[JoinPerm(r, from#JoinResponse(jr))] == jr) &&
  (forall r: Round, vr: VoteResponse ::
    voteChannel[r][vr] > 0 ==>
      domain#VoteResponseChannel(permVoteChannel)[VotePerm(r, from#VoteResponse(vr))] &&
      contents#VoteResponseChannel(permVoteChannel)[VotePerm(r, from#VoteResponse(vr))] == vr)
}

procedure {:yield_invariant} {:layer 1} YieldInv();
requires Inv(joinedNodes, voteInfo, acceptorState, permJoinChannel, permVoteChannel);

procedure {:yield_invariant} {:layer 1} YieldInvChannels();
requires {:layer 1} InvChannels(joinChannel, permJoinChannel, voteChannel, permVoteChannel);

////////////////////////////////////////////////////////////////////////////////

procedure {:yields}{:layer 1}{:refines "A_Paxos"} Paxos({:layer 1}{:linear_in "perm"} rs: [Round]bool)
requires {:layer 1} Init(rs, joinedNodes, voteInfo, decision, pendingAsyncs);
requires {:layer 1} InitLow(acceptorState, joinChannel, voteChannel, permJoinChannel, permVoteChannel);
{
  var r: int;
  var {:layer 1}{:linear "perm"} r_lin: int;
  var {:layer 1}{:linear "perm"} rs': [Round]bool;
  var {:layer 1}{:pending_async} PAs:[PA]int;

  r := 0;
  rs' := rs;
  while (*)
  invariant {:layer 1}{:cooperates} true;
  invariant {:layer 1} 0 <= r;
  invariant {:layer 1} (forall r': Round :: r < r' ==> rs'[r']);
  invariant {:layer 1} PAs == (lambda pa: PA :: if (is#A_StartRound(pa) && round#A_StartRound(pa) == round_lin#A_StartRound(pa) && Round(round#A_StartRound(pa)) && round#A_StartRound(pa) <= r) then 1 else 0);
  {
    r := r + 1;
    call rs', r_lin := ExtractRoundPermission(rs', r);
    async call StartRound(r, r_lin);
  }
  call AddPendingAsyncs(PAs);
}

procedure {:yields}{:layer 1}{:refines "A_StartRound"} StartRound(r: Round, {:layer 1}{:linear_in "perm"} r_lin: Round)
requires {:layer 1} Round(r) && r_lin == r;
requires {:layer 1} Inv(joinedNodes, voteInfo, acceptorState, permJoinChannel, permVoteChannel);
requires {:layer 1} InvChannels(joinChannel, permJoinChannel, voteChannel, permVoteChannel);
{
  var n: int;
  var {:layer 1}{:linear "perm"} p: Permission;
  var {:layer 1}{:linear "perm"} ps: [Permission]bool;
  var {:layer 1}{:linear "perm"} ps': [Permission]bool;
  var {:layer 1}{:pending_async} PAs:[PA]int;

  call ps, ps' := SplitPermissions(r_lin);
  n := 1;
  while (n <= numNodes)
  invariant {:layer 1}{:cooperates} true;
  invariant {:layer 1} 1 <= n && n <= numNodes+1;
  invariant {:layer 1} (forall n': Node :: n <= n' && n' <= numNodes ==> ps[JoinPerm(r, n')]);
  invariant {:layer 1} PAs == (lambda pa: PA :: if is#A_Join(pa) && round#A_Join(pa) == r && 1 <= node#A_Join(pa) && node#A_Join(pa) < n && p#A_Join(pa) == JoinPerm(round#A_Join(pa), node#A_Join(pa)) then 1 else 0);
  {
    call ps, p := ExtractJoinPermission(ps, r, n);
    async call Join(r, n, p);
    n := n + 1;
  }
  async call Propose(r, ps');
  call AddPendingAsyncs(PAs);
  call RemovePendingAsyncs(SingletonPA(A_StartRound(r, r_lin)));
}

procedure {:yields}{:layer 1}{:right} ProposeHelper(r: Round) returns (maxRound: Round, maxValue: Value, {:layer 1} ns: NodeSet)
modifies permJoinChannel, joinChannel;
requires {:layer 1} Round(r);
requires {:layer 1} Inv(joinedNodes, voteInfo, acceptorState, permJoinChannel, permVoteChannel);
requires {:layer 1} InvChannels(joinChannel, permJoinChannel, voteChannel, permVoteChannel);
ensures {:layer 1} maxRound == MaxRound(r, ns, voteInfo);
ensures {:layer 1} Round(maxRound) ==> maxValue == value#VoteInfo(t#Some(voteInfo[maxRound]));
ensures {:layer 1} IsSubset(ns, joinedNodes[r]) && IsQuorum(ns);
ensures {:layer 1} Inv(joinedNodes, voteInfo, acceptorState, permJoinChannel, permVoteChannel);
ensures {:layer 1} InvChannels(joinChannel, permJoinChannel, voteChannel, permVoteChannel);
{
  var count: int;
  var joinResponse: JoinResponse;
  var maxNode: Node;
  var {:layer 1}{:linear "perm"} receivedPermissions: [Permission]bool;
  var {:layer 1}{:linear "perm"} receivedPermission: Permission;

  call {:layer 1} ns := InitializeQuorum();
  call receivedPermissions := InitializePermissions();
  count := 0;
  maxRound := 0;
  while (true)
  invariant {:layer 1} count == Cardinality(ns);
  invariant {:layer 1} (forall x: Node :: ns[x] ==> Node(x));
  invariant {:layer 1} IsSubset(ns, joinedNodes[r]);
  invariant {:layer 1} receivedPermissions == (lambda x: Permission :: is#JoinPerm(x) && r#JoinPerm(x) == r && ns[n#JoinPerm(x)]);
  invariant {:layer 1} maxRound == MaxRound(r, ns, voteInfo);
  invariant {:layer 1} Round(maxRound) ==> maxValue == value#VoteInfo(t#Some(voteInfo[maxRound]));
  invariant {:layer 1} Inv(joinedNodes, voteInfo, acceptorState, permJoinChannel, permVoteChannel);
  invariant {:layer 1} InvChannels(joinChannel, permJoinChannel, voteChannel, permVoteChannel);
  {
    call joinResponse := ReceiveJoinResponse(r);
    call receivedPermission := ReceiveJoinResponseIntro(r, joinResponse);
    call {:layer 1} MaxRoundLemma(voteInfo, r, ns, SingletonNode(n#JoinPerm(receivedPermission)));
    call {:layer 1} ns := AddToQuorum(ns, n#JoinPerm(receivedPermission));
    call receivedPermissions := AddPermission(receivedPermissions, receivedPermission);
    count := count + 1;
    if (lastVoteRound#JoinResponse(joinResponse) > maxRound) {
      maxNode := from#JoinResponse(joinResponse);
      maxRound := lastVoteRound#JoinResponse(joinResponse);
      maxValue := lastVoteValue#JoinResponse(joinResponse);
    }
    if (2 * count > numNodes) {
      break;
    }
  }
}

procedure {:yields}{:layer 1}{:refines "A_Propose"} Propose(r: Round, {:layer 1}{:linear_in "perm"} ps: [Permission]bool)
requires {:layer 1} Round(r) && ps == ProposePermissions(r);
requires {:layer 1} InvChannels(joinChannel, permJoinChannel, voteChannel, permVoteChannel);
requires {:layer 1} Inv(joinedNodes, voteInfo, acceptorState, permJoinChannel, permVoteChannel);
{
  var maxRound: Round;
  var maxValue: Value;
  var {:layer 1} ns: NodeSet;
  var n: int;
  var {:layer 1}{:linear "perm"} ps': [Permission]bool;
  var {:layer 1}{:linear "perm"} p: Permission;
  var {:layer 1}{:linear "perm"} cp: Permission;
  var {:layer 1}{:pending_async} PAs:[PA]int;

  call maxRound, maxValue, ns := ProposeHelper(r);
  call ps', cp := SplitConcludePermission(r, ps);
  n := 1;
  while (n <= numNodes)
  invariant {:layer 1}{:cooperates} true;
  invariant {:layer 1} 1 <= n && n <= numNodes+1;
  invariant {:layer 1} (forall n': Node :: n <= n' && n' <= numNodes ==> ps'[VotePerm(r, n')]);
  invariant {:layer 1} PAs == (lambda pa: PA :: if is#A_Vote(pa) && round#A_Vote(pa) == r && 1 <= node#A_Vote(pa) && node#A_Vote(pa) < n && value#A_Vote(pa) == maxValue && p#A_Vote(pa) == VotePerm(round#A_Vote(pa), node#A_Vote(pa)) then 1 else 0);
  {
    call ps', p := ExtractVotePermission(ps', r, n);
    async call Vote(r, n, maxValue, p);
    n := n + 1;
  }
  async call Conclude(r, maxValue, cp);
  call ProposeIntro(r, maxValue);
  call AddPendingAsyncs(PAs);
  call RemovePendingAsyncs(SingletonPA(A_Propose(r, ps)));
}

procedure {:yields}{:layer 1}{:refines "A_Conclude"} Conclude(r: Round, v: Value, {:layer 1}{:linear_in "perm"} p: Permission)
requires {:layer 1} Round(r) && p == ConcludePerm(r);
requires {:layer 1} Inv(joinedNodes, voteInfo, acceptorState, permJoinChannel, permVoteChannel);
requires {:layer 1} InvChannels(joinChannel, permJoinChannel, voteChannel, permVoteChannel);
{
  var count: int;
  var voteResponse: VoteResponse;
  var {:layer 1} q: NodeSet;
  var {:linear "perm"} {:layer 1} receivedPermissions: [Permission]bool;
  var {:linear "perm"} {:layer 1} receivedPermission: Permission;

  call {:layer 1} q := InitializeQuorum();
  call receivedPermissions := InitializePermissions();
  count := 0;
  while (true)
  invariant {:layer 1} count == Cardinality(q);
  invariant {:layer 1} (forall x: Node :: q[x] ==> Node(x));
  invariant {:layer 1} IsSubset(q, ns#VoteInfo(t#Some(voteInfo[r])));
  invariant {:layer 1} receivedPermissions == (lambda x: Permission :: is#VotePerm(x) && r#VotePerm(x) == r && q[n#VotePerm(x)]);
  invariant {:layer 1} Inv(joinedNodes, voteInfo, acceptorState, permJoinChannel, permVoteChannel);
  invariant {:layer 1} InvChannels(joinChannel, permJoinChannel, voteChannel, permVoteChannel);
  {
    call voteResponse := ReceiveVoteResponse(r);
    call receivedPermission := ReceiveVoteResponseIntro(r, voteResponse);
    call {:layer 1} q := AddToQuorum(q, n#VotePerm(receivedPermission));
    call receivedPermissions := AddPermission(receivedPermissions, receivedPermission);
    count := count + 1;
    if (2 * count > numNodes) {
      call SetDecision(r, v);
      break;
    }
  }
  call RemovePendingAsyncs(SingletonPA(A_Conclude(r, v, p)));
}

procedure {:yields}{:layer 1}{:refines "A_Join"} Join(r: Round, n: Node, {:layer 1}{:linear_in "perm"} p: Permission)
requires {:layer 1} Round(r) && Node(n) && p == JoinPerm(r, n);
requires {:layer 1} Inv(joinedNodes, voteInfo, acceptorState, permJoinChannel, permVoteChannel);
{
  var doJoin: bool;
  var lastVoteRound: Round;
  var lastVoteValue: Value;

  call doJoin, lastVoteRound, lastVoteValue := JoinUpdate(r, n);
  if (doJoin) {
    call SendJoinResponse(r, n, lastVoteRound, lastVoteValue);
    call SendJoinResponseIntro(r, n, lastVoteRound, lastVoteValue, p);
    call JoinIntro(r, n);
  }
  call RemovePendingAsyncs(SingletonPA(A_Join(r, n, p)));
}

procedure {:yields}{:layer 1}{:refines "A_Vote"} Vote(r: Round, n: Node, v: Value, {:layer 1}{:linear_in "perm"} p: Permission)
requires {:layer 1} Round(r) && Node(n) && p == VotePerm(r, n);
requires {:layer 1} Inv(joinedNodes, voteInfo, acceptorState, permJoinChannel, permVoteChannel);
{
  var doVote:bool;

  call doVote := VoteRoundUpdate(r, n, v);
  if (doVote) {
    call SendVoteResponse(r, n);
    call SendVoteResponseIntro(r, n, p);
    call JoinIntro(r, n);
    call VoteIntro(r, n);
  }
  call RemovePendingAsyncs(SingletonPA(A_Vote(r, n, v, p)));
}

////////////////////////////////////////////////////////////////////////////////

procedure {:intro}{:layer 1} JoinIntro(r: Round, n: Node)
modifies joinedNodes;
{
  joinedNodes[r][n] := true;
}

procedure {:intro}{:layer 1} ProposeIntro(r: Round, v: Value)
modifies voteInfo;
{
  voteInfo[r] := Some(VoteInfo(v, NoNodes()));
}

procedure {:intro}{:layer 1} VoteIntro(r: Round, n: Node)
modifies voteInfo;
{
  voteInfo[r] := Some(VoteInfo(value#VoteInfo(t#Some(voteInfo[r])), ns#VoteInfo(t#Some(voteInfo[r]))[n := true]));
}

procedure {:intro}{:layer 1} AddPendingAsyncs(PAs: [PA]int)
modifies pendingAsyncs;
{
  pendingAsyncs := MapAdd(pendingAsyncs, PAs);
}

procedure {:intro}{:layer 1} RemovePendingAsyncs(PAs: [PA]int)
modifies pendingAsyncs;
{
  pendingAsyncs := MapSub(pendingAsyncs, PAs);
}

// Trusted lemmas for the proof of Propose and Conclude
procedure {:lemma} InitializeQuorum() returns (q: NodeSet);
ensures q == NoNodes();

procedure {:lemma} AddToQuorum(q: NodeSet, n: Node) returns (q': NodeSet);
requires !q[n];
ensures q' == q[n := true];
ensures Cardinality(q') == Cardinality(q) + 1;

procedure {:lemma} MaxRoundLemma(voteInfo:[Round]Option VoteInfo, r: Round, ns1: NodeSet, ns2: NodeSet);
requires Round(r);
ensures MaxRound(r, MapOr(ns1, ns2), voteInfo) ==
         if (MaxRound(r, ns1, voteInfo) < MaxRound(r, ns2, voteInfo))
         then MaxRound(r, ns2, voteInfo)
         else MaxRound(r, ns1, voteInfo);

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 1} A_SetDecision(round: Round, value: Value)
modifies decision;
{
  decision[round] := Some(value);
}

procedure {:atomic}{:layer 1} A_JoinUpdate(r: Round, n: Node)
returns (join:bool, lastVoteRound: Round, lastVoteValue: Value)
modifies acceptorState;
{
  var lastJoinRound: Round;
  lastJoinRound := lastJoinRound#AcceptorState(acceptorState[n]);
  if (r > lastJoinRound) {
    lastVoteRound := lastVoteRound#AcceptorState(acceptorState[n]);
    lastVoteValue := lastVoteValue#AcceptorState(acceptorState[n]);
    acceptorState[n] := AcceptorState(r, lastVoteRound, lastVoteValue);
    join := true;
  } else {
    join := false;
  }
}

procedure {:atomic}{:layer 1} A_VoteRoundUpdate(r: Round, n: Node, v: Value)
returns (vote:bool)
modifies acceptorState;
{
  var lastJoinRound: Round;
  lastJoinRound := lastJoinRound#AcceptorState(acceptorState[n]);
  if (r >= lastJoinRound) {
    acceptorState[n] := AcceptorState(r, r, v);
    vote := true;
  } else {
    vote := false;
  }
}

procedure {:yields}{:layer 0}{:refines "A_SetDecision"} SetDecision(round: Round, value: Value);
procedure {:yields}{:layer 0}{:refines "A_JoinUpdate"} JoinUpdate(r: Round, n: Node) returns (join:bool, lastVoteRound: Round, lastVoteValue: Value);
procedure {:yields}{:layer 0}{:refines "A_VoteRoundUpdate"} VoteRoundUpdate(r: Round, n: Node, v: Value) returns (vote:bool);

//// Channel send/receive actions

procedure {:left}{:layer 1} A_SendJoinResponse(round: Round, from: Node, lastVoteRound: Round, lastVoteValue: Value)
modifies joinChannel;
{
  joinChannel[round][JoinResponse(from, lastVoteRound, lastVoteValue)] := joinChannel[round][JoinResponse(from, lastVoteRound, lastVoteValue)] + 1;
}

procedure {:right}{:layer 1} A_ReceiveJoinResponse(round: Round)
returns (joinResponse: JoinResponse)
modifies joinChannel;
{
  assume joinChannel[round][joinResponse] > 0;
  joinChannel[round][joinResponse] := joinChannel[round][joinResponse] - 1;
}

procedure {:left}{:layer 1} A_SendVoteResponse(round: Round, from: Node)
modifies voteChannel;
{
  voteChannel[round][VoteResponse(from)] := voteChannel[round][VoteResponse(from)] + 1;
}

procedure {:right}{:layer 1} A_ReceiveVoteResponse(round: Round)
returns (voteResponse: VoteResponse)
modifies voteChannel;
{
  assume voteChannel[round][voteResponse] > 0;
  voteChannel[round][voteResponse] := voteChannel[round][voteResponse] - 1;
}

procedure {:yields}{:layer 0}{:refines "A_SendJoinResponse"}
SendJoinResponse(round: Round, from: Node, lastVoteRound: Round, lastVoteValue: Value);

procedure {:yields}{:layer 0}{:refines "A_ReceiveJoinResponse"}
ReceiveJoinResponse(round: Round) returns (joinResponse: JoinResponse);

procedure {:yields}{:layer 0}{:refines "A_SendVoteResponse"}
SendVoteResponse(round: Round, from: Node);

procedure {:yields}{:layer 0}{:refines "A_ReceiveVoteResponse"}
ReceiveVoteResponse(round: Round) returns (voteResponse: VoteResponse);

//// Introduction procedures to make send/receive more abstract

procedure {:intro}{:layer 1} SendJoinResponseIntro(round: Round, from: Node, lastVoteRound: Round, lastVoteValue: Value, {:linear_in "perm"} p: Permission)
modifies permJoinChannel;
{
  permJoinChannel := JoinResponseChannel(
    domain#JoinResponseChannel(permJoinChannel)[p := true],
    contents#JoinResponseChannel(permJoinChannel)[p := JoinResponse(from, lastVoteRound, lastVoteValue)]);
}

procedure {:intro}{:layer 1} ReceiveJoinResponseIntro(round: Round, joinResponse: JoinResponse) returns ({:linear "perm"} receivedPermission: Permission)
modifies permJoinChannel;
{
  assert domain#JoinResponseChannel(permJoinChannel)[JoinPerm(round, from#JoinResponse(joinResponse))];
  receivedPermission := JoinPerm(round, from#JoinResponse(joinResponse));
  permJoinChannel := JoinResponseChannel(domain#JoinResponseChannel(permJoinChannel)[receivedPermission := false], contents#JoinResponseChannel(permJoinChannel));
}

procedure {:intro}{:layer 1} SendVoteResponseIntro(round: Round, from: Node, {:linear_in "perm"} p: Permission)
modifies permVoteChannel;
{
  permVoteChannel := VoteResponseChannel(
    domain#VoteResponseChannel(permVoteChannel)[p := true],
    contents#VoteResponseChannel(permVoteChannel)[p := VoteResponse(from)]);
}

procedure {:intro}{:layer 1} ReceiveVoteResponseIntro(round: Round, voteResponse: VoteResponse)
returns ({:linear "perm"} receivedPermission: Permission)
modifies permVoteChannel;
{
  assert domain#VoteResponseChannel(permVoteChannel)[VotePerm(round, from#VoteResponse(voteResponse))];
  receivedPermission := VotePerm(round, from#VoteResponse(voteResponse));
  permVoteChannel := VoteResponseChannel(domain#VoteResponseChannel(permVoteChannel)[receivedPermission := false], contents#VoteResponseChannel(permVoteChannel));
}

//// Permission accounting

procedure {:intro}{:layer 1} ExtractRoundPermission({:linear_in "perm"} rs: [Round]bool, r: Round)
returns ({:linear "perm"} rs': [Round]bool, {:linear "perm"} r_lin: Round)
{
  assert rs[r];
  rs', r_lin := rs[r := false], r;
}

procedure {:intro}{:layer 1} SplitPermissions({:linear_in "perm"} r_lin: Round)
returns ({:linear "perm"} ps: [Permission]bool, {:linear "perm"} ps': [Permission]bool)
{
  ps, ps' := JoinPermissions(r_lin), ProposePermissions(r_lin);
}

procedure {:intro}{:layer 1} ExtractJoinPermission({:linear_in "perm"} ps: [Permission]bool, r: Round, n: Node)
returns ({:linear "perm"} ps': [Permission]bool, {:linear "perm"} p: Permission)
{
  assert ps[JoinPerm(r, n)];
  p := JoinPerm(r, n);
  ps' := ps[p := false];
}

procedure {:intro}{:layer 1} SplitConcludePermission(r: Round, {:linear_in "perm"} ps: [Permission]bool)
returns ({:linear "perm"} ps': [Permission]bool, {:linear "perm"} cp: Permission)
{
  assert ps == ProposePermissions(r);
  ps', cp := VotePermissions(r), ConcludePerm(r);
}

procedure {:intro}{:layer 1} ExtractVotePermission({:linear_in "perm"} ps: [Permission]bool, r: Round, n: Node)
returns ({:linear "perm"} ps': [Permission]bool, {:linear "perm"} p: Permission)
{
  assert ps[VotePerm(r, n)];
  p := VotePerm(r, n);
  ps' := ps[p := false];
}

procedure {:intro}{:layer 1} InitializePermissions()
returns ({:linear "perm"} receivedPermissions: [Permission]bool)
{
  receivedPermissions := MapConst(false);
}

procedure {:intro}{:layer 1} AddPermission({:linear_in "perm"} receivedPermissions: [Permission]bool, {:linear_in "perm"} p: Permission)
returns ({:linear "perm"}receivedPermissions': [Permission]bool)
{
  receivedPermissions' := receivedPermissions[p := true];
}

// Local Variables:
// flycheck-disabled-checkers: (boogie)
// End:
