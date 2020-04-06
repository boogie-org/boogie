procedure {:atomic}{:layer 3} A_Paxos'({:linear_in "perm"} rs: [Round]bool)
returns ()
modifies joinedNodes, voteInfo, decision, pendingAsyncs;
{
  assert Init(rs, joinedNodes, voteInfo, decision, pendingAsyncs);
  havoc joinedNodes, voteInfo, decision, pendingAsyncs;
  assume (forall r1: Round, r2: Round :: is#SomeValue(decision[r1]) && is#SomeValue(decision[r2]) ==> decision[r1] == decision[r2]);
}

procedure {:atomic}{:layer 2}
{:IS "A_Paxos'","INV"}
{:elim "A_StartRound","A_StartRound'"}
{:elim "A_Propose","A_Propose'"}
{:elim "A_Conclude","A_Conclude'"}
{:elim "A_Join","A_Join'"}
{:elim "A_Vote","A_Vote'"}
A_Paxos({:linear_in "perm"} rs: [Round]bool)
returns ({:pending_async "A_StartRound"} PAs:[PA]int)
modifies pendingAsyncs;
{
  var numRounds: int;
  assert Init(rs, joinedNodes, voteInfo, decision, pendingAsyncs);
  assert triggerRound(0);
  assume 0 <= numRounds;
  assume triggerRound(numRounds);
  PAs := (lambda pa: PA :: if is#StartRound_PA(pa) && round#StartRound_PA(pa) == round_lin#StartRound_PA(pa) && Round(round#StartRound_PA(pa)) && round#StartRound_PA(pa) <= numRounds then 1 else 0);
  pendingAsyncs := PAs;
}

function {:inline} FirstCasePAs(k: int, numRounds: int) : [PA]int
{
  (lambda pa: PA :: if (is#StartRound_PA(pa) && round#StartRound_PA(pa) == round_lin#StartRound_PA(pa) && k < round#StartRound_PA(pa) && round#StartRound_PA(pa) <= numRounds) then 1 else 0)
}

function {:inline} SecondCasePAs(k: int, m: Node, numRounds: int) : [PA]int
{
  (lambda pa : PA ::
    if (is#StartRound_PA(pa) && round#StartRound_PA(pa) == round_lin#StartRound_PA(pa) && k+1 < round#StartRound_PA(pa) && round#StartRound_PA(pa) <= numRounds) ||
       (pa == Propose_PA(k+1, ProposePermissions(k+1))) ||
       (is#Join_PA(pa) && round#Join_PA(pa) == k+1 && m < node#Join_PA(pa) && node#Join_PA(pa) <= numNodes &&
         p#Join_PA(pa) == JoinPerm(k+1, node#Join_PA(pa)))
    then 1 else 0)
}

function {:inline} SecondCaseChoice(k: int, m: Node) : PA
{
  if m == numNodes then Propose_PA(k+1, ProposePermissions(k+1)) else Join_PA(k+1, m+1, JoinPerm(k+1, m+1))
}

function {:inline} ThirdCasePAs(k: int, m: Node, v: Value, numRounds: int) : [PA]int
{
  ( lambda pa: PA ::
    if (is#StartRound_PA(pa) && round#StartRound_PA(pa) == round_lin#StartRound_PA(pa) && k+1 < round#StartRound_PA(pa) && round#StartRound_PA(pa) <= numRounds) ||
       (pa == Conclude_PA(k+1, v, ConcludePerm(k+1))) ||
       (is#Vote_PA(pa) && round#Vote_PA(pa) == k+1 && m < node#Vote_PA(pa) && node#Vote_PA(pa) <= numNodes &&
         value#Vote_PA(pa) == v && p#Vote_PA(pa) == VotePerm(k+1, node#Vote_PA(pa)))
    then 1 else 0)
}

function {:inline} ThirdCaseChoice(k: int, m: Node, v: Value) : PA
{
  if m == numNodes then Conclude_PA(k+1, v, ConcludePerm(k+1)) else Vote_PA(k+1, m+1, v, VotePerm(k+1, m+1))
}

procedure {:IS_invariant}{:layer 2} INV({:linear_in "perm"} rs: [Round]bool)
returns ({:pending_async "A_StartRound","A_Propose","A_Conclude","A_Join","A_Vote"} PAs:[PA]int, {:choice} choice:PA)
modifies joinedNodes, voteInfo, decision, pendingAsyncs;
{
  assert Init(rs, joinedNodes, voteInfo, decision, pendingAsyncs);

  havoc joinedNodes, voteInfo, decision;

  // This invariant is the "pending async skeleton" which states the possible
  // pending asyncs in the sequentialization. The existentially quantified k
  // denotes the number of rounds that already finished (i.e., rounds 1 to k
  // finished and k+1 is the round that currently executes), and similarly the
  // existentially quantified m denotes the number of nodes that already
  // finished in the current round.
  assume (exists k, numRounds: int :: {triggerRound(k), triggerRound(numRounds)} 0 <= k && k <= numRounds && triggerRound(numRounds) &&
    if k == numRounds then
    (
      PAs == NoPAs()
    )
    else
    (
      (
        PAs == FirstCasePAs(k, numRounds) &&
        choice == StartRound_PA(k+1, k+1) &&
        (forall r: Round :: r < 1 || r > k ==> joinedNodes[r] == NoNodes()) &&
        (forall r: Round :: r < 1 || r > k ==> is#NoneVoteInfo(voteInfo[r])) &&
        (forall r: Round :: r < 1 || r > k ==> is#NoneValue(decision[r]))
      )
      ||
      (
        (forall r: Round :: r < 1 || r > k+1 ==> joinedNodes[r] == NoNodes()) &&
        (forall r: Round :: r < 1 || r > k ==> is#NoneVoteInfo(voteInfo[r])) &&
        (forall r: Round :: r < 1 || r > k ==> is#NoneValue(decision[r])) &&
        (exists m: Node :: {triggerNode(m)} 0 <= m && m <= numNodes &&
          (forall n: Node :: n < 1 || n > m ==> !joinedNodes[k+1][n]) &&
          PAs == SecondCasePAs(k, m, numRounds) &&
          choice == SecondCaseChoice(k, m)
        )
      )
      ||
      (
        is#SomeVoteInfo(voteInfo[k+1]) &&
        (forall r: Round :: r < 1 || r > k+1 ==> joinedNodes[r] == NoNodes()) &&
        (forall r: Round :: r < 1 || r > k+1 ==> is#NoneVoteInfo(voteInfo[r])) &&
        (forall r: Round :: r < 1 || r > k ==> is#NoneValue(decision[r])) &&
        (exists m: Node :: {triggerNode(m)} 0 <= m && m <= numNodes &&
          (forall n: Node :: n < 1 || n > m ==> !ns#SomeVoteInfo(voteInfo[k+1])[n]) &&
          PAs == ThirdCasePAs(k, m, value#SomeVoteInfo(voteInfo[k+1]), numRounds) &&
          choice == ThirdCaseChoice(k, m, value#SomeVoteInfo(voteInfo[k+1]))
        )
      )
    )
  );

  // If there was a decision for some value, then there must have been a
  // proposal of the same value and a quorum of nodes that voted for it.
  assume (forall r: Round :: is#SomeValue(decision[r]) ==>
    is#SomeVoteInfo(voteInfo[r]) &&
    value#SomeVoteInfo(voteInfo[r]) == value#SomeValue(decision[r]) &&
    (exists q: NodeSet :: { IsSubset(q, ns#SomeVoteInfo(voteInfo[r])), IsQuorum(q) }
      IsSubset(q, ns#SomeVoteInfo(voteInfo[r])) && IsQuorum(q)));

  // This is the main invariant to prove
  assume (forall r1: Round, r2: Round :: is#SomeValue(decision[r1]) && r1 <= r2 && is#SomeVoteInfo(voteInfo[r2]) ==> value#SomeVoteInfo(voteInfo[r2]) == value#SomeValue(decision[r1]));

  // This is the main property to prove
  assume (forall r1: Round, r2: Round :: is#SomeValue(decision[r1]) && is#SomeValue(decision[r2]) ==> decision[r1] == decision[r2]);

  pendingAsyncs := PAs;
}

// Local Variables:
// flycheck-disabled-checkers: (boogie)
// End:
