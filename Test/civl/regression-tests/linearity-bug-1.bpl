// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} n : int;
var {:linear} {:layer 0,1} S : Set int;

// This test exposed a bug in the commutativity checker. Since t is linear_in,
// it does not have to be available after the atomic action executed. However,
// the disjointness expression in the antecedent of the postcondition of the
// commutativity checker procedure contained t and thus made the whole
// postcondition 'vacuously' (because t is added to A) true.

atomic action {:layer 1} atomic_inc_n ({:linear_in} t : One int)
modifies S, n;
{ call One_Put(S, t); n := n + 1; }

yield procedure {:layer 0} inc_n ({:linear_in} t : One int);
refines atomic_inc_n;

right action {:layer 1} atomic_read_n () returns (ret : int)
{ ret := n; }

yield procedure {:layer 0} read_n () returns (ret : int);
refines atomic_read_n;
