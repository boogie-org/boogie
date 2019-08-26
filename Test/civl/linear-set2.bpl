// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type X;
function {:builtin "MapConst"} MapConstInt(int) : [X]int;
function {:builtin "MapConst"} MapConstBool(bool) : [X]bool;
function {:builtin "MapOr"} MapOr([X]bool, [X]bool) : [X]bool;
function {:builtin "MapAnd"} MapAnd([X]bool, [X]bool) : [X]bool;

function {:inline} None() : [X]bool
{
    MapConstBool(false)
}

function {:inline} All() : [X]bool
{
    MapConstBool(true)
}

function {:inline} {:linear "x"} XCollector(xs: [X]bool) : [X]bool
{
  xs
}
function {:inline} {:linear "tid"} TidCollector(x: X) : [X]bool
{
  MapConstBool(false)[x := true]
}
function {:inline} {:linear "tid"} TidSetCollector(x: [X]bool) : [X]bool
{
  x
}

var {:layer 0,1} x: int;
var {:layer 0,1} l: X;
const nil: X;

var {:layer 0,1}{:linear "tid"} unallocated:[X]bool;

procedure {:yields} {:layer 1} Split({:linear_in "x"} xls: [X]bool) returns ({:linear "x"} xls1: [X]bool, {:linear "x"} xls2: [X]bool)
ensures {:layer 1} xls == MapOr(xls1, xls2) && xls1 != None() && xls2 != None();
{
  yield;
  call xls1, xls2 := SplitLow(xls);
  yield;
}

procedure {:yields} {:layer 1} Allocate() returns ({:linear "tid"} xls: X)
ensures {:layer 1} xls != nil;
{
  yield;
  call xls := AllocateLow();
  yield;
}

procedure {:atomic} {:layer 1} AtomicSet(v: int)
modifies x;
{ x := v; }

procedure {:yields} {:layer 0} {:refines "AtomicSet"} Set(v: int);

procedure {:atomic} {:layer 1} AtomicLock(tidls: X)
modifies l;
{ assume l == nil; l := tidls; }

procedure {:yields} {:layer 0} {:refines "AtomicLock"} Lock(tidls: X);

procedure {:atomic} {:layer 1} AtomicUnlock()
modifies l;
{ l := nil; }

procedure {:yields} {:layer 0} {:refines "AtomicUnlock"} Unlock();

procedure {:atomic} {:layer 1} AtomicSplitLow({:linear_in "x"} xls: [X]bool) returns ({:linear "x"} xls1: [X]bool, {:linear "x"} xls2: [X]bool)
{
  // xls == xls1 ⊎ xls2
  assume xls == MapOr(xls1, xls2);
  assume MapAnd(xls1, xls2) == None();
  assume xls1 != None();
  assume xls2 != None();
}

procedure {:yields} {:layer 0} {:refines "AtomicSplitLow"} SplitLow({:linear_in "x"} xls: [X]bool) returns ({:linear "x"} xls1: [X]bool, {:linear "x"} xls2: [X]bool);

procedure {:atomic} {:layer 1} AtomicAllocateLow() returns ({:linear "tid"} xls: X)
modifies unallocated;
{ assume xls != nil && unallocated[xls]; unallocated[xls] := false; }

procedure {:yields} {:layer 0} {:refines "AtomicAllocateLow"} AllocateLow() returns ({:linear "tid"} xls: X);

procedure {:yields} {:layer 1} main({:linear_in "tid"} tidls': X, {:linear_in "x"} xls': [X]bool)
requires {:layer 1} tidls' != nil && xls' == All();
{
    var {:linear "tid"} tidls: X;
    var {:linear "x"} xls: [X]bool;
    var {:linear "tid"} lsChild: X;
    var {:linear "x"} xls1: [X]bool;
    var {:linear "x"} xls2: [X]bool;

    tidls := tidls';
    xls := xls';

    yield;
    call Set(42);
    yield;
    assert {:layer 1} xls == All();
    assert {:layer 1} x == 42;
    call xls1, xls2 := Split(xls);
    call lsChild := Allocate();
    yield;
    async call thread(lsChild, xls1);
    call lsChild := Allocate();
    yield;
    async call thread(lsChild, xls2);
    yield;
}

procedure {:yields} {:layer 1} thread({:linear_in "tid"} tidls': X, {:linear_in "x"} xls': [X]bool)
requires {:layer 1} tidls' != nil && xls' != None();
{
    var {:linear "x"} xls: [X]bool;
    var {:linear "tid"} tidls: X;

    tidls := tidls';
    xls := xls';

    yield;
    call Lock(tidls);
    yield;
    assert {:layer 1} tidls != nil && xls != None();
    call Set(0);
    yield;
    assert {:layer 1} tidls != nil && xls != None();
    assert {:layer 1} x == 0;
    call Unlock();
    yield;
}
