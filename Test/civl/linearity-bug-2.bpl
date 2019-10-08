// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:linear "lin"} {:layer 1,2} set : [int]bool;

procedure {:atomic} {:layer 2} atomic_foo ({:linear "lin"} i : int)
modifies set;
{ set[i] := true; }

procedure {:yields} {:layer 1} {:refines "atomic_foo"} foo ({:linear "lin"} i : int);

procedure {:yields} {:layer 2} main ({:linear "lin"} i : int)
{
  yield;
  call foo(i);
  assert {:layer 2} false;
  yield;
}

// ###########################################################################
// Collectors for linear domains

function {:builtin "MapConst"} MapConstBool (bool) : [int]bool;

function {:inline} {:linear "lin"} Collector (x : int) : [int]bool
{ MapConstBool(false)[x := true] }

function {:inline} {:linear "lin"} SetCollector (x : [int]bool) : [int]bool
{ x }
