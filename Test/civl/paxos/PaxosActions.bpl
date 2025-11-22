function {:inline} JoinLt(r: Round, joinChannelPermissions: Set (One Permission), usedPermissions: Set (One Permission)): bool {
  (forall r': Round:: Round(r') && r' < r ==> Set_IsSubset(JoinPermissions(r'), Set_Union(joinChannelPermissions, usedPermissions)))
}

function {:inline} VoteLt(r: Round, voteChannelPermissions: Set (One Permission), usedPermissions: Set (One Permission)): bool {
  (forall r': Round:: Round(r') && r' < r ==> Set_IsSubset(VotePermissions(r'), Set_Union(voteChannelPermissions, usedPermissions)))
}

function {:inline} JoinLe(r: Round, joinChannelPermissions: Set (One Permission), usedPermissions: Set (One Permission)): bool {
  (forall r': Round:: Round(r') && r' <= r ==> Set_IsSubset(JoinPermissions(r'), Set_Union(joinChannelPermissions, usedPermissions)))
}

function {:inline} VoteLe(r: Round, voteChannelPermissions: Set (One Permission), usedPermissions: Set (One Permission)): bool {
  (forall r': Round:: Round(r') && r' <= r ==> Set_IsSubset(VotePermissions(r'), Set_Union(voteChannelPermissions, usedPermissions)))
}

invariant {:layer 2} JoinPre(r: Round);
preserves JoinLt(r, joinChannelPermissions, usedPermissions);
preserves VoteLt(r, voteChannelPermissions, usedPermissions);

invariant {:layer 2} JoinResponsePre(r: Round, {:linear} roundPermission: One Permission);
preserves roundPermission->val == RoundPerm(r);
preserves JoinLe(r, joinChannelPermissions, usedPermissions);
preserves VoteLt(r, voteChannelPermissions, usedPermissions);
preserves (exists joinPerm: Permission :: joinPerm->r == r && Node(joinPerm->n) && Set_Contains(joinChannelPermissions, One(joinPerm)));

invariant {:layer 2} VotePre(r: Round);
preserves JoinLe(r, joinChannelPermissions, usedPermissions);
preserves VoteLt(r, voteChannelPermissions, usedPermissions);

invariant {:layer 2} VoteResponsePre(r: Round, {:linear} roundPermission: One Permission);
preserves roundPermission->val == RoundPerm(r);
preserves JoinLe(r, joinChannelPermissions, usedPermissions);
preserves VoteLe(r, voteChannelPermissions, usedPermissions);
preserves (exists n: Node :: Node(n) && Set_Contains(voteChannelPermissions, One(VotePerm(r, n))));

left action {:layer 2} A_Join(r: Round, n: Node, {:linear_in} p: One Permission)
requires call JoinPre(r);
{
  assert Round(r) && Node(n);
  assert p->val == JoinPerm(r, n);

  assume
    {:add_to_pool "Round", r, r-1}
    {:add_to_pool "Node", n}
    true;

  if (*) {
    assume (forall r': Round :: Round(r') && joinInfo[r'][n] ==> r' < r);
    joinInfo[r][n] := true;
  }
  call One_Put(joinChannelPermissions, p);
}

left action {:layer 2} A_ProcessJoinResponse(r: Round, {:linear} roundPermission: One Permission, {:linear} votePermissions: Set (One Permission))
returns (joinResponse: JoinResponse)
requires call JoinResponsePre(r, roundPermission);
{
  var {:pool "A"} n: Node;
  var joinPerm: Permission;
  var {:pool "C"} lastVoteRound: int;
  var {:pool "B"} lastVoteValue: Value;

  assert Round(r) && roundPermission->val == RoundPerm(r) && votePermissions == VotePermissions(r);
  joinPerm := JoinPerm(r, n);
  assume Node(n) && Set_Contains(joinChannelPermissions, One(joinPerm));
  call joinChannelPermissions, usedPermissions := MovePermission(joinPerm, joinChannelPermissions, usedPermissions);
  if (*) {
    assume joinInfo[r][n];
    assume MaxRoundPredicate(r, n, voteInfo, lastVoteRound);
    if (lastVoteRound != 0) {
      assume !(status[lastVoteRound] is Inactive);
      lastVoteValue := status[lastVoteRound]->value;
    }
    joinResponse := JoinAccept(n, lastVoteRound, lastVoteValue);
  } else {
    joinResponse := JoinReject(n);
  }
}

left action {:layer 2} A_Vote(r: Round, n: Node, v: Value, {:linear_in} p: One Permission)
requires call VotePre(r);
{
  assert Round(r) && Node(n);
  assert p->val == VotePerm(r, n);
  assert IsActive(status[r], v);
  assert !voteInfo[r][n];

  assume
    {:add_to_pool "Round", r, r-1}
    {:add_to_pool "Node", n}
    true;

  if (*) {
    assume (forall r': Round :: Round(r') && joinInfo[r'][n] ==> r' <= r);
    voteInfo[r][n] := true;
    joinInfo[r][n] := true;
  }
  call One_Put(voteChannelPermissions, p);
}

left action {:layer 2} A_ProcessVoteResponse(r: Round, {:linear} roundPermission: One Permission) returns (voteResponse: VoteResponse)
requires call VoteResponsePre(r, roundPermission);
{
  var {:pool "A"} n: Node;
  var votePerm: Permission;

  assert Round(r) && roundPermission->val == RoundPerm(r);
  votePerm := VotePerm(r, n);
  assume Node(n) && Set_Contains(voteChannelPermissions, One(votePerm));
  call voteChannelPermissions, usedPermissions := MovePermission(votePerm, voteChannelPermissions, usedPermissions);
  if (voteInfo[r][n]) {
    voteResponse := VoteAccept(n);
  } else {
    voteResponse := VoteReject(n);
  }
}
