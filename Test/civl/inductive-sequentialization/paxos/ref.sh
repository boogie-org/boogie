#!/bin/bash

# RUN: %boogie -useArrayTheory -lib -monomorphize Paxos.bpl PaxosActions.bpl PaxosImpl.bpl > "%t"
# RUN: %diff "%s.expect" "%t"

boogie -nologo -useArrayTheory -lib -monomorphize $@ Paxos.bpl PaxosActions.bpl PaxosImpl.bpl
