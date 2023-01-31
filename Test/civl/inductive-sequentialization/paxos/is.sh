#!/bin/bash

# RUN: %parallel-boogie Paxos.bpl PaxosActions.bpl PaxosAbstractions.bpl PaxosSeq.bpl > "%t"
# RUN: %diff "%s.expect" "%t"

boogie $@ /lib:base Paxos.bpl PaxosActions.bpl PaxosAbstractions.bpl PaxosSeq.bpl
