async atomic action {:layer 2} A_StartRound(r: Round, {:linear_in} r_lin: Set Permission)
creates A_Join, A_Propose;
{
  assert AllPermissions(r) == r_lin;
  assert Round(r);

  assume
    {:add_to_pool "Round", r-1}
    {:add_to_pool "Node", 0}
    {:add_to_pool "Permission", ConcludePerm(r)}
    true;

  call create_asyncs(JoinPAs(r));
  call create_async(A_Propose(r, ProposePermissions(r)));
}

async atomic action {:layer 2} A_Propose(r: Round, {:linear_in} ps: Set Permission)
creates A_Vote, A_Conclude;
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
    call create_async(A_Conclude(r, maxValue, One(ConcludePerm(r))));
  }
}

async atomic action {:layer 2} A_Conclude(r: Round, v: Value, {:linear_in} p: One Permission)
modifies decision;
{
  var {:pool "NodeSet"} q: NodeSet;

  assert Round(r);
  assert p->val == ConcludePerm(r);
  assert voteInfo[r] is Some;
  assert voteInfo[r]->t->value == v;

  assume {:add_to_pool "Round", r} {:add_to_pool "NodeSet", q} true;

  if (*) {
    assume IsSubset(q, voteInfo[r]->t->ns) && IsQuorum(q);
    decision[r] := Some(v);
  }
}

async atomic action {:layer 2} A_Join(r: Round, n: Node, {:linear_in} p: One Permission)
modifies joinedNodes;
{
  assert Round(r);
  assert p->val == JoinPerm(r, n);

  assume
    {:add_to_pool "Round", r, r-1}
    {:add_to_pool "Node", n}
    true;

  if (*) {
    assume (forall r': Round :: Round(r') && joinedNodes[r'][n] ==> r' < r);
    joinedNodes[r][n] := true;
  }
}

async atomic action {:layer 2} A_Vote(r: Round, n: Node, v: Value, {:linear_in} p: One Permission)
modifies joinedNodes, voteInfo;
{
  assert Round(r);
  assert p->val == VotePerm(r, n);
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
