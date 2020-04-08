// RUN: %boogie -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:linear "lin"} {:layer 1,2} set : [int]bool;

procedure {:atomic} {:layer 2} atomic_foo ({:linear "lin"} i : int)
modifies set;
{ set[i] := true; }

// ###########################################################################
// Collectors for linear domains

function {:builtin "MapConst"} MapConstBool (bool) : [int]bool;

function {:inline} {:linear "lin"} Collector (x : int) : [int]bool
{ MapConstBool(false)[x := true] }

function {:inline} {:linear "lin"} SetCollector (x : [int]bool) : [int]bool
{ x }
