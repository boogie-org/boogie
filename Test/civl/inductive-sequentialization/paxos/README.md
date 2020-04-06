* `Paxos.bpl`: Shared definitions (types, consts, functions, axioms, shared vars)
* `PaxosActions.bpl`: Atomic actions of event handlers
* `PaxosAbstractions.bpl`: Abstractions of atomic actions used in the IS proof
* `PaxosSeq.bpl`: IS proof
* `PaxosSeqAxioms.bpl`: Axioms (really lemmas) about quorums and function MaxRound
* `PaxosImpl.bpl`: Low-level implementation

Both `PaxosImpl.bpl` and `PaxosSeq.bpl` contain a definition of action `A_Paxos`
(the latter has the additional annotations for IS).

When working on the IS proof, run Boogie on (script `is.sh`):

```
Paxos.bpl PaxosSeqAxioms.bpl PaxosActions.bpl PaxosAbstractions.bpl PaxosSeq.bpl
```

When working on the refinement proof, run Boogie on (script `ref.sh`):

```
Paxos.bpl PaxosActions.bpl PaxosImpl.bpl
```
