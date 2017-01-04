

// The linearity annotation of foo is not valid, since the value of i has to be
// available upon return, but the action adds the value to set.
// TODO: Implement at check! Otherwise the injected linearity assumption for foo
// is inconsistent and allows us to prove false in main.

var {:linear "lin"} {:layer 1,2} set : [int]bool;

procedure {:yields} {:layer 1,2} foo ({:linear "lin"} i : int);
ensures {:atomic} |{
 A: set[i] := true;
    return true;
}|;

procedure {:yields} {:layer 2} main ({:linear "lin"} i : int)
ensures {:atomic} |{ A: return true; }|;
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
