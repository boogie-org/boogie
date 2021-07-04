#!/bin/bash

# RUN: %boogie Paxos.bpl PaxosSeqAxioms.bpl PaxosActions.bpl PaxosAbstractions.bpl PaxosSeq.bpl > "%t"
# RUN: %diff "%s.expect" "%t"

boogie $@ Paxos.bpl PaxosSeqAxioms.bpl PaxosActions.bpl PaxosAbstractions.bpl PaxosSeq.bpl
