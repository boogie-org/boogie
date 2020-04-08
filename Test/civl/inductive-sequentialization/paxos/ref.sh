#!/bin/bash

# RUN: %boogie -typeEncoding:m -useArrayTheory Paxos.bpl PaxosActions.bpl PaxosImpl.bpl > "%t"
# RUN: %diff "%s.expect" "%t"

boogie -nologo -typeEncoding:m -useArrayTheory $@ Paxos.bpl PaxosActions.bpl PaxosImpl.bpl
