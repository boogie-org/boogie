// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} n : int;
var {:linear "tid"} {:layer 0,1} S : TidSet;

// This test exposed a bug in the commutativity checker. Since t is linear_in,
// it does not have to be available after the atomic action executed. However,
// the disjointness expression in the antecedent of the postcondition of the
// commutativity checker procedure contained t and thus made the whole
// postcondition 'vacuously' (because t is added to A) true.

action {:layer 1} atomic_inc_n ({:linear_in "tid"} t : Tid)
modifies S, n;
{ assert !S[t]; S[t] := true; n := n + 1; }

yield procedure {:layer 0} inc_n ({:linear_in "tid"} t : Tid) refines atomic_inc_n;

-> action {:layer 1} atomic_read_n () returns (ret : int)
{ ret := n; }

yield procedure {:layer 0} read_n () returns (ret : int) refines atomic_read_n;

type {:linear "tid"} Tid = int;
type TidSet = [Tid]bool;
