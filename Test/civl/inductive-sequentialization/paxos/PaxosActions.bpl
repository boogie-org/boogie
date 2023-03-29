procedure {:atomic}{:layer 2}
{:pending_async} {:creates "A_Join", "A_Propose"}
A_StartRound(r: Round, {:linear_in "perm"} r_lin: Round)
{
  assert r == r_lin;
  assert Round(r);

  assume
    {:add_to_pool "Round", r-1}
    {:add_to_pool "Node", 0}
    {:add_to_pool "Permission", ConcludePerm(r)}
    true;

  call create_asyncs(JoinPAs(r));
  call create_async(A_Propose(r, ProposePermissions(r)));
}

procedure {:atomic}{:layer 2}
{:pending_async} {:creates "A_Vote", "A_Conclude"}
A_Propose(r: Round, {:linear_in "perm"} ps: [Permission]bool)
modifies voteInfo;
{
  var {:pool "Round"} maxRound: int;
  var {:pool "MaxValue"} maxValue: Value;
  var {:pool "NodeSet"} ns: NodeSet;

  assert Round(r);
  assert ps == ProposePermissions(r);
  assert voteInfo[r] is None;

  assume
    {:add_to_pool "Round", r, r-1}
    {:add_to_pool "Node", 0}
    {:add_to_pool "NodeSet", ns}
    {:add_to_pool "Permission", ConcludePerm(r)}
    true;

  if (*) {
    assume IsSubset(ns, joinedNodes[r]) && IsQuorum(ns);
    maxRound := MaxRound(r, ns, voteInfo);
    if (maxRound != 0)
    {
      maxValue := voteInfo[maxRound]->t->value;
    }
    voteInfo[r] := Some(VoteInfo(maxValue, NoNodes()));
    call create_asyncs(VotePAs(r, maxValue));
    call create_async(A_Conclude(r, maxValue, ConcludePerm(r)));
  }
}

procedure {:atomic}{:layer 2}
{:pending_async}
A_Conclude(r: Round, v: Value, {:linear_in "perm"} p: Permission)
modifies decision;
{
  var {:pool "NodeSet"} q: NodeSet;

  assert Round(r);
  assert p == ConcludePerm(r);
  assert voteInfo[r] is Some;
  assert voteInfo[r]->t->value == v;

  assume {:add_to_pool "Round", r} true;

  if (*) {
    assume IsSubset(q, voteInfo[r]->t->ns) && IsQuorum(q);
    decision[r] := Some(v);
  }
}

procedure {:atomic}{:layer 2}
{:pending_async}
A_Join(r: Round, n: Node, {:linear_in "perm"} p: Permission)
modifies joinedNodes;
{
  assert Round(r);
  assert p == JoinPerm(r, n);

  assume
    {:add_to_pool "Round", r, r-1}
    {:add_to_pool "Node", n}
    true;

  if (*) {
    assume (forall r': Round :: Round(r') && joinedNodes[r'][n] ==> r' < r);
    joinedNodes[r][n] := true;
  }
}

procedure {:atomic}{:layer 2}
{:pending_async}
A_Vote(r: Round, n: Node, v: Value, {:linear_in "perm"} p: Permission)
modifies joinedNodes, voteInfo;
{
  assert Round(r);
  assert p == VotePerm(r, n);
  assert voteInfo[r] is Some;
  assert voteInfo[r]->t->value == v;
  assert !voteInfo[r]->t->ns[n];

  assume
    {:add_to_pool "Round", r, r-1}
    {:add_to_pool "Node", n}
    true;

  if (*) {
    assume (forall r': Round :: Round(r') && joinedNodes[r'][n] ==> r' <= r);
    voteInfo[r] := Some(VoteInfo(v, voteInfo[r]->t->ns[n := true]));
    joinedNodes[r][n] := true;
  }
}

// Local Variables:
// flycheck-disabled-checkers: (boogie)
// End:
