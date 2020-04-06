function {:inline}{:lemma}{:commutativity "A_Propose", "A_Propose'"}
CommutativityLemma_A_Propose_A_Propose'(voteInfo: [Round]OptionVoteInfo, first_r: Round, second_r: Round) : bool
{
  Lemma_MaxRound_InitVote(voteInfo, first_r, second_r) &&
  Lemma_MaxRound_InitVote(voteInfo, second_r, first_r)
}

function {:inline}{:lemma}{:commutativity "A_Vote", "A_Propose'"}
CommutativityLemma_A_Vote_A_Propose'(voteInfo: [Round]OptionVoteInfo, first_r: Round, second_r: Round, first_n: Node) : bool
{
  Lemma_MaxRound_AddNodeToVote(voteInfo, second_r, first_r, first_n)
}

function {:inline}{:lemma}{:commutativity "A_Propose", "A_Vote'"}
CommutativityLemma_A_Propose_A_Vote'(voteInfo: [Round]OptionVoteInfo, first_r: Round, second_r: Round, second_n: Node) : bool
{
  Lemma_MaxRound_AddNodeToVote(voteInfo, first_r, second_r, second_n)
}

axiom (forall ns1: NodeSet, ns2: NodeSet :: {IsQuorum(ns1), IsQuorum(ns2)}
  IsQuorum(ns1) && IsQuorum(ns2) ==> (exists n: Node :: Node(n) && ns1[n] && ns2[n])
);

// Local Variables:
// flycheck-disabled-checkers: (boogie)
// End:
