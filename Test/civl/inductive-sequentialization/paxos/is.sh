#!/bin/bash

# RUN: %boogie -useArrayTheory -lib -monomorphize Paxos.bpl PaxosSeqAxioms.bpl PaxosActions.bpl PaxosAbstractions.bpl PaxosSeq.bpl -proverOpt:O:smt.random_seed=100 > "%t"
# RUN: %diff "%s.expect" "%t"

boogie -nologo -useArrayTheory -lib -monomorphize $@ Paxos.bpl PaxosSeqAxioms.bpl PaxosActions.bpl PaxosAbstractions.bpl PaxosSeq.bpl
