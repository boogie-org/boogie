////////////////////////////////////////////////////////////////////////////////
//// Entry procedure

yield atomic procedure {:layer 2} Paxos({:layer 1,2}{:linear_in} ps: Set (One Permission))
requires {:layer 1,2} ps->val == (lambda p: One Permission :: true);
requires {:layer 2} (forall r: Round :: Round(r) ==> status[r] == Inactive() && voteInfo[r] == MapConst(false));
preserves call YieldInv();
{
  var r: int;
  var {:layer 1,2}{:linear} ps': Set (One Permission);
  var {:layer 1,2}{:linear} allRoundPermissions: Set (One Permission);

  r := 1;
  ps' := ps;
  while (*)
  invariant {:layer 1,2} Round(r);
  invariant {:layer 1,2} (forall r': Round :: r <= r' ==> Set_IsSubset(AllPermissions(r'), ps'));
  invariant {:layer 2} (forall r': Round :: r <= r' ==> status[r'] == Inactive() && voteInfo[r'] == MapConst(false));
  invariant {:layer 2} JoinLt(r, joinChannelPermissions, usedPermissions);
  invariant {:layer 2} VoteLt(r, voteChannelPermissions, usedPermissions);
  invariant {:layer 2} VoteQuorumLt(r, status, voteInfo);
  invariant {:layer 2} SpecLt(r, status);
  {
    allRoundPermissions := AllPermissions(r);
    call {:layer 1,2} Set_Get(ps', allRoundPermissions);
    async call {:sync} ExecuteRound(r, allRoundPermissions);
    r := r + 1;
  }
}

////////////////////////////////////////////////////////////////////////////////
//// Proposer procedures

yield left procedure {:layer 2} ExecuteRound(r: Round, {:layer 1,2}{:linear_in} allRoundPermissions: Set (One Permission))
requires {:layer 1,2} Round(r) && allRoundPermissions == AllPermissions(r);
preserves call YieldInv();
requires {:layer 2} status[r] == Inactive() && voteInfo[r] == MapConst(false);
ensures {:layer 2} status == old(status)[r := status[r]] && voteInfo == old(voteInfo)[r := voteInfo[r]];
requires {:layer 2} JoinLt(r, joinChannelPermissions, usedPermissions);
requires {:layer 2} VoteLt(r, voteChannelPermissions, usedPermissions);
ensures {:layer 2} JoinLe(r, joinChannelPermissions, usedPermissions);
ensures {:layer 2} VoteLe(r, voteChannelPermissions, usedPermissions);
requires {:layer 2} VoteQuorumLt(r, status, voteInfo);
requires {:layer 2} SpecLt(r, status);
ensures {:layer 2} VoteQuorumLe(r, status, voteInfo);
ensures {:layer 2} SpecLe(r, status);
{
  var {:layer 1,2}{:linear} roundPermission: One Permission;
  var {:layer 1,2}{:linear} joinPermissions: Set (One Permission);
  var {:layer 1,2}{:linear} votePermissions: Set (One Permission);
  var {:layer 2} joinPerms: Set (One Permission);
  var maxRound: Round;
  var maxValue: Value;
  var count: int;
  var {:layer 2} joinAcceptPerms: Set (One Permission);

  call {:layer 1,2} roundPermission, joinPermissions, votePermissions := SplitPermissions(r, allRoundPermissions);
  call joinPerms := SendJoinRequests(r, joinPermissions);
  call maxRound, maxValue, count, joinAcceptPerms := CollectJoinResponses(r, roundPermission, votePermissions, joinPerms);
  if (2 * count > numNodes) {
    call {:layer 2} SpecProof(r, maxRound, maxValue, joinAcceptPerms, status, voteInfo);
    call UpdateStatusToProposed(r, maxValue, roundPermission, votePermissions) | YieldInv();
    call Propose(r, maxValue, roundPermission, votePermissions);
  } else {
    call DropPermissions(votePermissions) | YieldInv();
  }
}

yield left procedure {:layer 2} SendJoinRequests(
  r: Round, {:layer 1,2}{:linear_in} joinPermissions: Set (One Permission)) returns ({:layer 2} joinPerms: Set (One Permission))
preserves call YieldInv();
requires {:layer 1,2} Round(r) && joinPermissions == JoinPermissions(r);
requires {:layer 2} JoinLt(r, joinChannelPermissions, usedPermissions);
requires {:layer 2} VoteLt(r, voteChannelPermissions, usedPermissions);
ensures {:layer 2} JoinLe(r, joinChannelPermissions, usedPermissions);
ensures {:layer 2} joinPerms == Set_Intersection(JoinPermissions(r), joinChannelPermissions);
ensures {:layer 2} Set_Size(joinPerms) == numNodes;
{
  var n: int;
  var {:layer 1,2}{:linear} joinPermissions': Set (One Permission);
  var {:layer 1,2}{:linear} p: One Permission;

  joinPermissions' := joinPermissions;
  n := 1;
  call {:layer 2} joinPerms := Copy(Set_Empty());
  while (n <= numNodes)
  invariant {:layer 1,2} 1 <= n && n <= numNodes+1;
  invariant {:layer 1,2} (forall n': Node :: n <= n' && n' <= numNodes ==> Set_Contains(joinPermissions', One(JoinPerm(r, n'))));
  invariant {:layer 2} joinPerms == Set_Intersection(JoinPermissions(r), joinChannelPermissions);
  invariant {:layer 2} Set_Size(joinPerms) == n - 1;
  invariant {:layer 2} JoinLt(r, joinChannelPermissions, usedPermissions);
  invariant {:layer 2} Set_IsSubset(JoinPermissionsUpto(r, n), Set_Union(joinChannelPermissions, usedPermissions));
  {
    p := One(JoinPerm(r, n));
    call {:layer 1,2} One_Get(joinPermissions', p);
    assert {:layer 2} JoinLt(r, joinChannelPermissions, usedPermissions);
    async call {:sync} Join(r, n, p);
    call {:layer 2} joinPerms := Lemma_SetSize_Add(joinPerms, p);
    n := n + 1;
  }
}

pure procedure SpecProof(r: Round, maxRound: Round, maxValue: Value, joinAcceptPerms: Set (One Permission), status: [Round]RoundStatus, voteInfo: [Round]NodeSet)
requires Round(r);
requires VoteQuorumLt(r, status, voteInfo);
requires SpecLt(r, status);
requires IsJoinQuorum(r, joinAcceptPerms);
requires maxRound == 0 || (Round(maxRound) && maxRound < r && IsActive(status[maxRound], maxValue));
requires (forall n: Node, r': Round:: Set_Contains(joinAcceptPerms, One(JoinPerm(r, n))) && maxRound < r' && r' < r ==> !voteInfo[r'][n]);
ensures (forall r': Round:: Round(r') && r' < r && status[r'] is Decided ==> status[r']->value == maxValue); // actual spec
{
  call Lemma_Quorum_Intersection(r, joinAcceptPerms, status, voteInfo);
  assert (forall r': Round:: Round(r') && r' < r && status[r'] is Decided ==> r' <= maxRound);
}

yield left procedure {:layer 2} CollectJoinResponses(
  r: Round, {:layer 1,2}{:linear} roundPermission: One Permission, {:layer 1,2}{:linear} votePermissions: Set (One Permission), {:layer 2} joinPerms: Set (One Permission))
returns (maxRound: Round, maxValue: Value, count: int, {:layer 2} joinAcceptPerms: Set (One Permission))
requires {:layer 1,2} Round(r) && roundPermission->val == RoundPerm(r) && votePermissions == VotePermissions(r);
preserves call YieldInv();
requires {:layer 2} joinPerms == Set_Intersection(JoinPermissions(r), joinChannelPermissions);
requires {:layer 2} Set_Size(joinPerms) == numNodes;
requires {:layer 2} JoinLe(r, joinChannelPermissions, usedPermissions);
ensures {:layer 2} JoinLe(r, joinChannelPermissions, usedPermissions);
requires {:layer 2} VoteLt(r, voteChannelPermissions, usedPermissions);
ensures {:layer 2} VoteLt(r, voteChannelPermissions, usedPermissions);
ensures {:layer 2} count == Set_Size(joinAcceptPerms);
ensures {:layer 2} (forall p: One Permission:: Set_Contains(joinAcceptPerms, p) ==> Set_Contains(JoinPermissions(r), p));
ensures {:layer 2} maxRound == 0 || (Round(maxRound) && maxRound < r && IsActive(status[maxRound], maxValue));
ensures {:layer 2} (forall n: Node, r': Round:: Set_Contains(joinAcceptPerms, One(JoinPerm(r, n))) && maxRound < r' && r' < r ==> !voteInfo[r'][n]);
{
  var n: int;
  var joinResponse: JoinResponse;
  var {:layer 2} joinPerms': Set (One Permission);

  n := 0;
  count := 0;
  maxRound := 0;
  joinPerms' := joinPerms;
  call {:layer 2} joinAcceptPerms := Copy(Set_Empty());
  while (n < numNodes)
  invariant {:layer 1} {:yields} true;
  invariant {:layer 1,2} 0 <= n && n <= numNodes;
  invariant call YieldInv();
  invariant {:layer 2} joinPerms' == Set_Intersection(JoinPermissions(r), joinChannelPermissions);
  invariant {:layer 2} Set_Size(joinPerms') + n == numNodes;
  invariant {:layer 2} JoinLe(r, joinChannelPermissions, usedPermissions);
  invariant {:layer 2} VoteLt(r, voteChannelPermissions, usedPermissions);
  invariant {:layer 2} count == Set_Size(joinAcceptPerms);
  invariant {:layer 2} Set_IsSubset(joinAcceptPerms, usedPermissions);
  invariant {:layer 2} (forall p: One Permission:: Set_Contains(joinAcceptPerms, p) ==> Set_Contains(JoinPermissions(r), p));
  invariant {:layer 2} maxRound == 0 || (Round(maxRound) && maxRound < r && IsActive(status[maxRound], maxValue));
  invariant {:layer 2} (forall n: Node, r': Round:: Set_Contains(joinAcceptPerms, One(JoinPerm(r, n))) && maxRound < r' && r' < r ==> !voteInfo[r'][n]);
  {
    call joinResponse := ProcessJoinResponse(r, roundPermission, votePermissions);
    call {:layer 2} joinPerms' := Lemma_SetSize_Remove(joinPerms', One(JoinPerm(r, joinResponse->from)));
    if (joinResponse is JoinAccept) {
      call {:layer 2} joinAcceptPerms := Lemma_SetSize_Add(joinAcceptPerms, One(JoinPerm(r, joinResponse->from)));
      count := count + 1;
      if (joinResponse->lastVoteRound > maxRound) {
        maxRound := joinResponse->lastVoteRound;
        maxValue := joinResponse->lastVoteValue;
      }
      if (2 * count > numNodes) {
        break;
      }
    }
    n := n + 1;
  }
}

yield procedure {:layer 1} UpdateStatusToProposed(
  r: Round, v: Value, {:layer 1}{:linear} roundPermission: One Permission, {:layer 1}{:linear} votePermissions: Set (One Permission))
refines left action {:layer 2} _ {
  assert Round(r) && roundPermission->val == RoundPerm(r) && votePermissions == VotePermissions(r);
  assert voteInfo[r] == MapConst(false);
  assert status[r] == Inactive();
  status[r] := Proposed(v);
} 
{
  assert {:layer 1} voteInfo[r] == MapConst(false);
  call {:layer 1} status := Copy(status[r := Proposed(v)]);
}

yield procedure {:layer 1} DropPermissions({:layer 1}{:linear_in} ps: Set (One Permission))
refines left action {:layer 2} _ {
  call Set_Put(usedPermissions, ps);
}
{
  call {:layer 1} Set_Put(usedPermissions, ps);
}

yield left procedure {:layer 2} Propose(
  r: Round, v: Value, {:layer 1,2}{:linear_in} roundPermission: One Permission, {:layer 1,2}{:linear_in} votePermissions: Set (One Permission))
requires {:layer 1,2} Round(r) && roundPermission->val == RoundPerm(r) && votePermissions == VotePermissions(r);
preserves call YieldInv();
requires {:layer 2} status[r] == Proposed(v) && voteInfo[r] == MapConst(false);
ensures {:layer 2} status == old(status)[r := status[r]] && voteInfo == old(voteInfo)[r := voteInfo[r]];
requires {:layer 2} JoinLe(r, joinChannelPermissions, usedPermissions);
ensures {:layer 2} JoinLe(r, joinChannelPermissions, usedPermissions);
requires {:layer 2} VoteLt(r, voteChannelPermissions, usedPermissions);
ensures {:layer 2} VoteLe(r, voteChannelPermissions, usedPermissions);
requires {:layer 2} VoteQuorumLt(r, status, voteInfo);
requires {:layer 2} SpecLe(r, status);
ensures {:layer 2} VoteQuorumLe(r, status, voteInfo);
ensures {:layer 2} SpecLe(r, status);
{
  var n: int;
  var {:layer 1,2}{:linear} ps': Set (One Permission);
  var {:layer 1,2}{:linear} p: One Permission;
  var {:layer 2} votePerms: Set (One Permission);
  var count: int;
  var {:layer 2} voteAcceptPerms: Set (One Permission);

  ps' := votePermissions;
  n := 1;
  call {:layer 2} votePerms := Copy(Set_Empty());
  while (n <= numNodes)
  invariant {:layer 1,2} 1 <= n && n <= numNodes+1;
  invariant {:layer 1,2} (forall n': Node :: n <= n' && n' <= numNodes ==> Set_Contains(ps', One(VotePerm(r, n'))));
  invariant {:layer 2} (forall n': Node :: n <= n' && n' <= numNodes ==> !voteInfo[r][n']);
  invariant {:layer 2} voteInfo == old(voteInfo)[r := voteInfo[r]];
  invariant {:layer 2} votePerms == Set_Intersection(VotePermissions(r), voteChannelPermissions);
  invariant {:layer 2} Set_Size(votePerms) == n - 1;
  invariant {:layer 2} JoinLe(r, joinChannelPermissions, usedPermissions);
  invariant {:layer 2} VoteLt(r, voteChannelPermissions, usedPermissions);
  invariant {:layer 2} Set_IsSubset(VotePermissionsUpto(r, n), Set_Union(voteChannelPermissions, usedPermissions));
  {
    p := One(VotePerm(r, n));
    call {:layer 1,2} One_Get(ps', p);
    async call {:sync} Vote(r, n, v, p);
    call {:layer 2} votePerms := Lemma_SetSize_Add(votePerms, p);
    n := n + 1;
  }
  call count, voteAcceptPerms := CollectVoteResponses(r, v, roundPermission, votePerms);
  if (2 * count > numNodes)
  {
    call {:layer 2} Lemma_Quorum_Monotonic(r, voteAcceptPerms, voteInfo[r]);
    call UpdateStatusToDecided(r, roundPermission, v) | YieldInv();
  }
}

yield left procedure {:layer 2} CollectVoteResponses(
  r: Round, v: Value, {:layer 1,2}{:linear} roundPermission: One Permission, {:layer 2} votePerms: Set (One Permission))
  returns (count: int, {:layer 2} voteAcceptPerms: Set (One Permission))
requires {:layer 1,2} Round(r) && roundPermission->val == RoundPerm(r);
preserves call YieldInv();
requires {:layer 2} status[r] == Proposed(v);
ensures {:layer 2} status == old(status)[r := status[r]] && voteInfo == old(voteInfo)[r := voteInfo[r]];
requires {:layer 2} votePerms == Set_Intersection(VotePermissions(r), voteChannelPermissions);
requires {:layer 2} Set_Size(votePerms) == numNodes;
requires {:layer 2} JoinLe(r, joinChannelPermissions, usedPermissions);
ensures {:layer 2} JoinLe(r, joinChannelPermissions, usedPermissions);
requires {:layer 2} VoteLe(r, voteChannelPermissions, usedPermissions);
ensures {:layer 2} VoteLe(r, voteChannelPermissions, usedPermissions);
ensures {:layer 2} count == Set_Size(voteAcceptPerms);
ensures {:layer 2} (forall p: One Permission:: Set_Contains(voteAcceptPerms, p) ==> Set_Contains(VotePermissions(r), p) && voteInfo[p->val->r][p->val->n]);
{
  var n: int;
  var voteResponse: VoteResponse;
  var {:layer 2} votePerms': Set (One Permission);
  
  n := 0;
  count := 0;
  votePerms' := votePerms;
  call {:layer 2} voteAcceptPerms := Copy(Set_Empty());
  while (n < numNodes)
  invariant {:layer 1} {:yields} true;
  invariant {:layer 1} 0 <= n && n <= numNodes;
  invariant call YieldInv();
  invariant {:layer 2} votePerms' == Set_Intersection(VotePermissions(r), voteChannelPermissions);
  invariant {:layer 2} Set_Size(votePerms') + n == numNodes;
  invariant {:layer 2} JoinLe(r, joinChannelPermissions, usedPermissions);
  invariant {:layer 2} VoteLe(r, voteChannelPermissions, usedPermissions);
  invariant {:layer 2} count == Set_Size(voteAcceptPerms);
  invariant {:layer 2} (forall p: One Permission:: Set_Contains(voteAcceptPerms, p) ==> Set_Contains(VotePermissions(r), p) && voteInfo[p->val->r][p->val->n]);
  invariant {:layer 2} Set_IsSubset(voteAcceptPerms, usedPermissions);
  {
    call voteResponse := ProcessVoteResponse(r, roundPermission);
    call {:layer 2} votePerms' := Lemma_SetSize_Remove(votePerms', One(VotePerm(r, voteResponse->from)));
    if (voteResponse is VoteAccept) {
      call {:layer 2} voteAcceptPerms := Lemma_SetSize_Add(voteAcceptPerms, One(VotePerm(r, voteResponse->from)));
      count := count + 1;
      if (2 * count > numNodes) {
        break;
      }
    }
    n := n + 1;
  }
}

yield procedure {:layer 1} UpdateStatusToDecided(r: Round, {:layer 1}{:linear} roundPermission: One Permission, v: Value)
refines left action {:layer 2} _ {
  assert Round(r) && roundPermission->val == RoundPerm(r);
  assert status[r] == Proposed(v);
  status[r] := Decided(v);
}
{
  assert {:layer 1} status[r] == Proposed(v);
  call {:layer 1} status := Copy(status[r := Decided(v)]);
}

yield procedure {:layer 1}
ProcessJoinResponse(r: Round, {:linear}{:layer 1} roundPermission: One Permission, {:layer 1}{:linear} votePermissions: Set (One Permission)) returns (joinResponse: JoinResponse)
refines A_ProcessJoinResponse;
preserves call YieldInv();
{
  call joinResponse := ReceiveJoinResponse(r);
  assume {:add_to_pool "A", joinResponse->from} {:add_to_pool "B", joinResponse->lastVoteValue} true;
  assume {:add_to_pool "C", MaxRound(r, joinResponse->from, voteInfo)} true;
  call {:layer 1} joinChannelPermissions, usedPermissions := MovePermission(JoinPerm(r, joinResponse->from), joinChannelPermissions, usedPermissions);
}

yield procedure {:layer 1}
ProcessVoteResponse(r: Round, {:linear}{:layer 1} roundPermission: One Permission) returns (voteResponse: VoteResponse)
refines A_ProcessVoteResponse;
preserves call YieldInv();
{
  call voteResponse := ReceiveVoteResponse(r);
  assume {:add_to_pool "A", voteResponse->from} true;
  call {:layer 1} voteChannelPermissions, usedPermissions := MovePermission(VotePerm(r, voteResponse->from), voteChannelPermissions, usedPermissions);
}

yield procedure {:layer 0} ReceiveJoinResponse(round: Round) returns (joinResponse: JoinResponse);
refines right action {:layer 1} _
{
  assume joinChannel[round][joinResponse] > 0;
  joinChannel[round][joinResponse] := joinChannel[round][joinResponse] - 1;
}


yield procedure {:layer 0} ReceiveVoteResponse(round: Round) returns (voteResponse: VoteResponse);
refines right action {:layer 1} _
{
  assume voteChannel[round][voteResponse] > 0;
  voteChannel[round][voteResponse] := voteChannel[round][voteResponse] - 1;
}

////////////////////////////////////////////////////////////////////////////////
//// Acceptor procedures

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
    call {:layer 1} joinInfo := Copy(joinInfo[r := joinInfo[r][n := true]]);
  }
  call {:layer 1} One_Put(joinChannelPermissions, p);
}

yield procedure {:layer 1}
Vote(r: Round, n: Node, v: Value, {:layer 1}{:linear_in} p: One Permission)
refines A_Vote;
requires {:layer 1} Round(r) && Node(n) && p->val == VotePerm(r, n);
requires call YieldInv();
{
  var voteResponse: VoteResponse;

  assert {:layer 1} IsActive(status[r], v);
  assert {:layer 1} !voteInfo[r][n];
  call voteResponse := VoteUpdate(r, n, v);
  call SendVoteResponse(r, voteResponse);
  if (voteResponse is VoteAccept) {
    call {:layer 1} joinInfo := Copy(joinInfo[r := joinInfo[r][n := true]]);
    call {:layer 1} voteInfo := Copy(voteInfo[r := voteInfo[r][n := true]]);
  }
  call {:layer 1} One_Put(voteChannelPermissions, p);
}

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

yield procedure {:layer 0} SendJoinResponse(round: Round, joinResponse: JoinResponse);
refines left action {:layer 1} _
{
  joinChannel[round][joinResponse] := joinChannel[round][joinResponse] + 1;
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

yield procedure {:layer 0} SendVoteResponse(round: Round, voteResponse: VoteResponse);
refines left action {:layer 1} _
{
  voteChannel[round][voteResponse] := voteChannel[round][voteResponse] + 1;
}

////////////////////////////////////////////////////////////////////////////////
//// Permission transfers

pure action SplitPermissions(r: Round, {:linear_in} allRoundPermissions: Set (One Permission))
returns ({:linear} roundPermission: One Permission, {:linear} joinPermissions: Set (One Permission), {:linear} votePermissions: Set (One Permission))
{
  var {:linear} ps: Set (One Permission);

  ps := allRoundPermissions;
  roundPermission := One(RoundPerm(r));
  call One_Get(ps, roundPermission);
  joinPermissions := JoinPermissions(r);
  call Set_Get(ps, joinPermissions);
  votePermissions := VotePermissions(r);
  call Set_Get(ps, votePermissions);
}

pure action MovePermission(p: Permission, {:linear_in} from: Set (One Permission), {:linear_in} to: Set (One Permission))
returns ({:linear} from': Set (One Permission), {:linear} to': Set (One Permission))
{
  var {:linear} one_p: One Permission;

  from' := from;
  to' := to;
  one_p := One(p);
  call One_Get(from', one_p);
  call One_Put(to', one_p);
}
