// RUN: %boogie -noinfer -useArrayTheory -typeEncoding:m "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0} n : int;
var {:linear "tid"} {:layer 0} S : TidSet;

// This test exposed a bug in the commutativity checker. Since t is linear_in,
// it does not have to be available after the atomic action executed. However,
// the disjointness expression in the antecedent of the postcondition of the
// commutativity checker procedure contained t and thus made the whole
// postcondition 'vacuously' (because t is added to A) true.

procedure {:yields} {:layer 0} inc_n ({:linear_in "tid"} t : Tid);
ensures {:atomic} |{
 A: assert !S[t];
    S[t] := true;
    n := n + 1;
    return true;
}|;

procedure {:yields} {:layer 0} read_n () returns (ret : int);
ensures {:right} |{ A: ret := n; return true; }|;

// ###########################################################################
// Linear permissions

type Tid = int;
type TidSet = [Tid]bool;

function {:builtin "MapConst"} MapConstBool (bool) : [Tid]bool;

function {:inline} {:linear "tid"} TidCollector (x : Tid) : [Tid]bool
{ MapConstBool(false)[x := true] }

function {:inline} {:linear "tid"} TidSetCollector (x : [Tid]bool) : [Tid]bool
{ x }
