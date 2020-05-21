#!/bin/bash

# RUN: %boogie -useArrayTheory Paxos.bpl PaxosActions.bpl PaxosImpl.bpl > "%t"
# RUN: %diff "%s.expect" "%t"

boogie -nologo -useArrayTheory $@ Paxos.bpl PaxosActions.bpl PaxosImpl.bpl
