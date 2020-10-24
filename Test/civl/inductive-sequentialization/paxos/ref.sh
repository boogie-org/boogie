#!/bin/bash

# RUN: %boogie Paxos.bpl PaxosActions.bpl PaxosImpl.bpl > "%t"
# RUN: %diff "%s.expect" "%t"

boogie -nologo $@ Paxos.bpl PaxosActions.bpl PaxosImpl.bpl
