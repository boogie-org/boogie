// RUN: %boogie -noinfer -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:linear "x"} {:layer 0} A : [int]bool;

procedure {:yields} {:layer 1} Proc ({:linear "x"} i: int)
{
  par Yield0() | Yield1();
  call Lemma(i);
  yield;
}

procedure {:yields} {:layer 0} Yield0 () { yield; }
procedure {:yields} {:layer 1} Yield1 () { yield; }

procedure Lemma (i: int);
requires !A[i];

// Collectors for linear domains

function {:builtin "MapConst"} MapConstBool(bool): [int]bool;
function {:builtin "MapOr"} MapOr([int]bool, [int]bool) : [int]bool;

function {:inline} {:linear "x"} Collector(i: int) : [int]bool
{
  MapConstBool(false)[i := true]
}
function {:inline} {:linear "x"} SetCollector(i: [int]bool) : [int]bool
{
  i
}
