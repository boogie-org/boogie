#!/bin/bash

# RUN: %boogie -proverOpt:O:smt.random_seed=10 Paxos.bpl PaxosSeqAxioms.bpl PaxosActions.bpl PaxosAbstractions.bpl PaxosSeq.bpl > "%t"
# RUN: %diff "%s.expect" "%t"

boogie -proverOpt:O:smt.random_seed=10 $@ Paxos.bpl PaxosSeqAxioms.bpl PaxosActions.bpl PaxosAbstractions.bpl PaxosSeq.bpl
