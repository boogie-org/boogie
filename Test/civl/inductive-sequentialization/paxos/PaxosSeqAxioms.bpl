function {:inline}{:lemma}{:commutativity "A_Propose", "A_Propose'"}
CommutativityLemma_A_Propose_A_Propose'(voteInfo: [Round]Option VoteInfo, first_r: Round, second_r: Round) : bool
{
  Lemma_MaxRound_InitVote(voteInfo, first_r, second_r) &&
  Lemma_MaxRound_InitVote(voteInfo, second_r, first_r)
}

axiom (forall ns1: NodeSet, ns2: NodeSet :: {IsQuorum(ns1), IsQuorum(ns2)}
  IsQuorum(ns1) && IsQuorum(ns2) ==> (exists n: Node :: Node(n) && ns1[n] && ns2[n])
);

// Local Variables:
// flycheck-disabled-checkers: (boogie)
// End:
