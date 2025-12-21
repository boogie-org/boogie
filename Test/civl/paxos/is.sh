#!/bin/bash

# RUN: %parallel-boogie Paxos.bpl PaxosActions.bpl PaxosImpl.bpl /lib:set_size /timeLimit:120 > "%t"
# RUN: %diff "%s.expect" "%t"

boogie $@ /lib:set_size Paxos.bpl PaxosActions.bpl PaxosImpl.bpl
