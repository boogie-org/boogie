#!/bin/bash

# RUN: %boogie Paxos.bpl PaxosSeqAxioms.bpl PaxosActions.bpl PaxosAbstractions.bpl PaxosSeq.bpl -proverOpt:O:smt.random_seed=100 > "%t"
# RUN: %diff "%s.expect" "%t"

boogie -nologo $@ Paxos.bpl PaxosSeqAxioms.bpl PaxosActions.bpl PaxosAbstractions.bpl PaxosSeq.bpl
