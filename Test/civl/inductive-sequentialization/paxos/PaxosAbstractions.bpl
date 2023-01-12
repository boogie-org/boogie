// Notes on the IS proof (is.sh)
/*
The IS proof for Paxos has two components---commutativity and invariance. Parts of the
specification are needed for one or the other component of the overall proof.

The abstractions of the atomic actions specified in this file only add extra gates,
which state facts about permissions and pending asyncs. These strengthened gates are
needed for commutativity checks. The facts about permissions and pending asyncs seem similar
but there is no redundancy because permission distribution is guaranteed in all executions
but the facts about pending asyncs hold only in sequentialized executions.
Permissions are needed only for the commutativity proof. The facts about pending asyncs
are needed for both commutativity and invariance proofs.

joinedNodes is a component of the abstract state at layer 2 but it is not needed for
the invariance proof. It is needed only to prove that A_Vote'(r', n, _, _) commutes to the
left of A_Propose(r, _). The strengthened gate of A_Vote' allows us to assume that r > r'.
There is a proof obligation only if n \in ns, the witness for the execution of A_Propose(r, _).
A contradiction is created since A_Propose(r, _) forces n to have joined r whereas
A_Vote'(r', n, _, _) forces n to not have joined any round greater than r'.
*/

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
  assert voteInfo[r] is None;

  /**************************************************************************/
  assert (forall r': Round :: r' <= r ==> pendingAsyncs[A_StartRound(r', r')] == 0);
  assert (forall r': Round, n': Node, p': Permission :: r' <= r ==> pendingAsyncs[A_Join(r', n', p')] == 0);
  assert (forall r': Round, p': [Permission]bool :: r' < r ==> pendingAsyncs[A_Propose(r', p')] == 0);
  assert (forall r': Round, n': Node, v': Value, p': Permission :: r' <= r ==> pendingAsyncs[A_Vote(r', n', v', p')] == 0);
  /**************************************************************************/

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

procedure {:IS_abstraction}{:layer 2} A_Conclude'(r: Round, v: Value, {:linear_in "perm"} p: Permission)
modifies decision, pendingAsyncs;
{
  assert (forall n': Node, v': Value, p': Permission :: pendingAsyncs[A_Vote(r, n', v', p')] == 0);

  call A_Conclude(r, v, p);
}

procedure {:IS_abstraction}{:layer 2} A_Join'(r: Round, n: Node, {:linear_in "perm"} p: Permission)
modifies joinedNodes, pendingAsyncs;
{
  assert (forall r': Round :: r' <= r ==> pendingAsyncs[A_StartRound(r', r')] == 0);
  assert (forall r': Round, n': Node, p': Permission :: r' < r ==> pendingAsyncs[A_Join(r', n', p')] == 0);
  assert (forall r': Round, p': [Permission]bool :: r' < r ==> pendingAsyncs[A_Propose(r', p')] == 0);
  assert (forall r': Round, n': Node, v': Value, p': Permission :: r' < r ==> pendingAsyncs[A_Vote(r', n', v', p')] == 0);

  call A_Join(r, n, p);
}

procedure {:IS_abstraction}{:layer 2} A_Vote'(r: Round, n: Node, v: Value, {:linear_in "perm"} p: Permission)
modifies joinedNodes, voteInfo, pendingAsyncs;
{
  assert (forall r': Round :: r' <= r ==> pendingAsyncs[A_StartRound(r', r')] == 0);
  assert (forall r': Round, n': Node, p': Permission :: r' <= r ==> pendingAsyncs[A_Join(r', n', p')] == 0);
  assert (forall r': Round, p': [Permission]bool :: r' <= r ==> pendingAsyncs[A_Propose(r', p')] == 0);
  assert (forall r': Round, n': Node, v': Value, p': Permission :: r' < r ==> pendingAsyncs[A_Vote(r', n', v', p')] == 0);

  call A_Vote(r, n, v, p);
}

// Local Variables:
// flycheck-disabled-checkers: (boogie)
// End:
