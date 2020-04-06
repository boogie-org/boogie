#!/bin/bash

# RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory Paxos.bpl PaxosSeqAxioms.bpl PaxosActions.bpl PaxosAbstractions.bpl PaxosSeq.bpl > "%t"
# RUN: %diff "%s.expect" "%t"

boogie -nologo -noinfer -typeEncoding:m -useArrayTheory $@ Paxos.bpl PaxosSeqAxioms.bpl PaxosActions.bpl PaxosAbstractions.bpl PaxosSeq.bpl
