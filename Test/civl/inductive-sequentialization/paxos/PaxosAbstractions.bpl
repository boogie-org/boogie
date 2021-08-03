procedure {:IS_abstraction}{:layer 2} A_StartRound'(r: Round, {:linear_in "perm"} r_lin: Round)
returns ({:pending_async "A_Join", "A_Propose"} PAs:[PA]int)
modifies pendingAsyncs;
{
  assert r == r_lin;
  assert Round(r);
  assert pendingAsyncs[A_StartRound(r, r_lin)] > 0;

  /**************************************************************************/
  // Hint for left mover checks
  assert
    {:add_to_pool "Round", r-1}
    {:add_to_pool "Node", 0}
    RoundCollector(r)[ConcludePerm(r)];
  /**************************************************************************/

  PAs := MapAdd(JoinPAs(r), SingletonPA(A_Propose(r, ProposePermissions(r))));

  pendingAsyncs := MapAdd(pendingAsyncs, PAs);
  pendingAsyncs := MapSub(pendingAsyncs, SingletonPA(A_StartRound(r, r_lin)));
}

procedure {:IS_abstraction}{:layer 2} A_Propose'(r: Round, {:linear_in "perm"} ps: [Permission]bool)
returns ({:pending_async "A_Vote", "A_Conclude"} PAs:[PA]int)
modifies voteInfo, pendingAsyncs;
{
  var {:pool "Round"} maxRound: int;
  var maxValue: Value;
  var {:pool "NodeSet"} ns: NodeSet;

  assert Round(r);
  assert pendingAsyncs[A_Propose(r, ps)] > 0;
  assert ps == ProposePermissions(r);
  assert is#None(voteInfo[r]);

  /**************************************************************************/
  assert (forall r': Round :: r' <= r ==> pendingAsyncs[A_StartRound(r', r')] == 0);
  assert (forall r': Round, n': Node, p': Permission :: r' <= r ==> pendingAsyncs[A_Join(r', n', p')] == 0);
  // Hint for commutativity w.r.t. {Paxos, Propose}
  assert
    {:add_to_pool "Round", r, r-1}
    {:add_to_pool "Node", 0}
    ps[ConcludePerm(r)];
  /**************************************************************************/

  assume
    {:add_to_pool "NodeSet", ns}
    true;

  if (*) {
    assume IsSubset(ns, joinedNodes[r]) && IsQuorum(ns);
    maxRound := MaxRound(r, ns, voteInfo);
    if (maxRound != 0)
    {
      maxValue := value#VoteInfo(t#Some(voteInfo[maxRound]));
    }
    voteInfo[r] := Some(VoteInfo(maxValue, NoNodes()));
    PAs := MapAdd(VotePAs(r, maxValue), SingletonPA(A_Conclude(r, maxValue, ConcludePerm(r))));
  } else {
    PAs := NoPAs();
  }

  pendingAsyncs := MapAdd(pendingAsyncs, PAs);
  pendingAsyncs := MapSub(pendingAsyncs, SingletonPA(A_Propose(r, ps)));
}

procedure {:IS_abstraction}{:layer 2} A_Conclude'(r: Round, v: Value, {:linear_in "perm"} p: Permission)
modifies decision, pendingAsyncs;
{
  var q: NodeSet;

  assert Round(r);
  assert pendingAsyncs[A_Conclude(r, v, p)] > 0;
  assert p == ConcludePerm(r);
  assert is#Some(voteInfo[r]);
  assert value#VoteInfo(t#Some(voteInfo[r])) == v;

  /**************************************************************************/
  assert
    {:add_to_pool "Round", r}
    (forall n': Node, v': Value, p': Permission :: pendingAsyncs[A_Vote(r, n', v', p')] == 0);
  /**************************************************************************/

  if (*) {
    assume IsSubset(q, ns#VoteInfo(t#Some(voteInfo[r]))) && IsQuorum(q);
    decision[r] := Some(v);
  }

  pendingAsyncs := MapSub(pendingAsyncs, SingletonPA(A_Conclude(r, v, p)));
}

procedure {:IS_abstraction}{:layer 2} A_Join'(r: Round, n: Node, {:linear_in "perm"} p: Permission)
modifies joinedNodes, pendingAsyncs;
{
  assert Round(r);
  assert pendingAsyncs[A_Join(r, n, p)] > 0;
  assert p == JoinPerm(r, n);

  /**************************************************************************/
  assert (forall r': Round :: r' <= r ==> pendingAsyncs[A_StartRound(r', r')] == 0);
  assert (forall r': Round, n': Node, p': Permission :: r' < r ==> pendingAsyncs[A_Join(r', n', p')] == 0);
  assert (forall r': Round, p': [Permission]bool :: r' < r ==> pendingAsyncs[A_Propose(r', p')] == 0);
  assert (forall r': Round, n': Node, v': Value, p': Permission :: r' < r ==> pendingAsyncs[A_Vote(r', n', v', p')] == 0);
  /**************************************************************************/

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

procedure {:IS_abstraction}{:layer 2} A_Vote'(r: Round, n: Node, v: Value, {:linear_in "perm"} p: Permission)
modifies joinedNodes, voteInfo, pendingAsyncs;
{
  assert Round(r);
  assert p == VotePerm(r, n);
  assert pendingAsyncs[A_Vote(r, n, v, p)] > 0;
  assert is#Some(voteInfo[r]);
  assert value#VoteInfo(t#Some(voteInfo[r])) == v;
  assert !ns#VoteInfo(t#Some(voteInfo[r]))[n];

  /**************************************************************************/
  assert (forall r': Round :: r' <= r ==> pendingAsyncs[A_StartRound(r', r')] == 0);
  assert (forall r': Round, n': Node, p': Permission :: r' <= r ==> pendingAsyncs[A_Join(r', n', p')] == 0);
  assert (forall r': Round, p': [Permission]bool :: r' <= r ==> pendingAsyncs[A_Propose(r', p')] == 0);
  assert (forall r': Round, n': Node, v': Value, p': Permission :: r' < r ==> pendingAsyncs[A_Vote(r', n', v', p')] == 0);
  /**************************************************************************/

  assume
    {:add_to_pool "Round", r, r-1}
    {:add_to_pool "Node", n}
    true;
  if (*) {
    assume (forall r': Round :: Round(r') && joinedNodes[r'][n] ==> r' <= r);
    voteInfo[r] := Some(VoteInfo(v, ns#VoteInfo(t#Some(voteInfo[r]))[n := true]));
    joinedNodes[r][n] := true;
  }

  pendingAsyncs := MapSub(pendingAsyncs, SingletonPA(A_Vote(r, n, v, p)));
}

// Local Variables:
// flycheck-disabled-checkers: (boogie)
// End:
