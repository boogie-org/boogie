#!/bin/bash

# RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory Paxos.bpl PaxosActions.bpl PaxosImpl.bpl > "%t"
# RUN: %diff "%s.expect" "%t"

boogie -nologo -noinfer -typeEncoding:m -useArrayTheory $@ Paxos.bpl PaxosActions.bpl PaxosImpl.bpl
