// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:linear "lin"} {:layer 1,2} set : [int]bool;

procedure {:atomic} {:layer 2} atomic_foo ({:linear "lin"} i : int)
modifies set;
{ set[i] := true; }

type {:linear "lin"} X = int;
