procedure {:atomic}{:layer 2} A_StartRound(r: Round, {:linear_in "perm"} r_lin: Round)
returns ({:pending_async "A_Join", "A_Propose"} PAs:[PA]int)
modifies pendingAsyncs;
{
  assert r == r_lin;
  assert Round(r);
  assert pendingAsyncs[A_StartRound(r, r_lin)] > 0;

  assume 
    {:add_to_pool "Round", r-1}
    {:add_to_pool "Node", 0}
    {:add_to_pool "Permission", ConcludePerm(r)}
    true;

  PAs := MapAdd(JoinPAs(r), SingletonPA(A_Propose(r, ProposePermissions(r))));

  pendingAsyncs := MapAdd(pendingAsyncs, PAs);
  pendingAsyncs := MapSub(pendingAsyncs, SingletonPA(A_StartRound(r, r_lin)));
}

procedure {:atomic}{:layer 2} A_Propose(r: Round, {:linear_in "perm"} ps: [Permission]bool)
returns ({:pending_async "A_Vote", "A_Conclude"} PAs:[PA]int)
modifies voteInfo, pendingAsyncs;
{
  var {:pool "Round"} maxRound: int;
  var maxValue: Value;
  var {:pool "NodeSet"} ns: NodeSet;

  assert Round(r);
  assert pendingAsyncs[A_Propose(r, ps)] > 0;
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
    PAs := MapAdd(VotePAs(r, maxValue), SingletonPA(A_Conclude(r, maxValue, ConcludePerm(r))));
  } else {
    PAs := NoPAs();
  }

  pendingAsyncs := MapAdd(pendingAsyncs, PAs);
  pendingAsyncs := MapSub(pendingAsyncs, SingletonPA(A_Propose(r, ps)));
}

procedure {:atomic}{:layer 2} A_Conclude(r: Round, v: Value, {:linear_in "perm"} p: Permission)
modifies decision, pendingAsyncs;
{
  var q: NodeSet;

  assert Round(r);
  assert pendingAsyncs[A_Conclude(r, v, p)] > 0;
  assert p == ConcludePerm(r);
  assert voteInfo[r] is Some;
  assert voteInfo[r]->t->value == v;

  assume 
    {:add_to_pool "Round", r}
    true;

  if (*) {
    assume IsSubset(q, voteInfo[r]->t->ns) && IsQuorum(q);
    decision[r] := Some(v);
  }

  pendingAsyncs := MapSub(pendingAsyncs, SingletonPA(A_Conclude(r, v, p)));
}

procedure {:atomic}{:layer 2} A_Join(r: Round, n: Node, {:linear_in "perm"} p: Permission)
modifies joinedNodes, pendingAsyncs;
{
  assert Round(r);
  assert pendingAsyncs[A_Join(r, n, p)] > 0;
  assert p == JoinPerm(r, n);

  assume
    {:add_to_pool "Round", r, r-1}
    {:add_to_pool "Node", n}
    true;

  if (*) {
    assume (forall r': Round :: Round(r') && joinedNodes[r'][n] ==> r' < r);
    joinedNodes[r][n] := true;
  }

  pendingAsyncs := MapSub(pendingAsyncs, SingletonPA(A_Join(r, n, p)));
}

procedure {:atomic}{:layer 2} A_Vote(r: Round, n: Node, v: Value, {:linear_in "perm"} p: Permission)
modifies joinedNodes, voteInfo, pendingAsyncs;
{
  assert Round(r);
  assert p == VotePerm(r, n);
  assert pendingAsyncs[A_Vote(r, n, v, p)] > 0;
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

  pendingAsyncs := MapSub(pendingAsyncs, SingletonPA(A_Vote(r, n, v, p)));
}

// Local Variables:
// flycheck-disabled-checkers: (boogie)
// End:
