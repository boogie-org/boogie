// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type X;
function {:builtin "MapConst"} MapConstInt(int) : [X]int;
function {:builtin "MapConst"} MapConstBool(bool) : [X]bool;
function {:builtin "MapOr"} MapOr([X]bool, [X]bool) : [X]bool;

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

var {:phase 1} x: int;
var {:phase 1} l: [X]bool;

procedure Split({:linear_in "x"} xls: [X]bool) returns ({:linear "x"} xls1: [X]bool, {:linear "x"} xls2: [X]bool);
ensures xls == MapOr(xls1, xls2) && xls1 != None() && xls2 != None();

procedure Allocate() returns ({:linear "tid"} xls: [X]bool);

procedure {:yields} {:phase 0,1} Set(v: int);
ensures {:atomic} |{A: x := v; return true; }|;

procedure {:yields} {:phase 0,1} Lock(tidls: [X]bool);
ensures {:atomic} |{A: assume l == None(); l := tidls; return true; }|;

procedure {:yields} {:phase 0,1} Unlock();
ensures {:atomic} |{A: l := None(); return true; }|;


procedure {:yields} {:phase 1} main({:linear_in "tid"} tidls': [X]bool, {:linear_in "x"} xls': [X]bool) 
requires {:phase 1} tidls' != None() && xls' == All();
{
    var {:linear "tid"} tidls: [X]bool;
    var {:linear "x"} xls: [X]bool;
    var {:linear "tid"} lsChild: [X]bool;
    var {:linear "x"} xls1: [X]bool;
    var {:linear "x"} xls2: [X]bool;

    tidls := tidls';
    xls := xls';
    yield;
    call Set(42);
    yield;
    assert {:phase 1} xls == All();
    assert {:phase 1} x == 42;
    call xls1, xls2 := Split(xls);
    call lsChild := Allocate();
    assume (lsChild != None());
    yield;
    async call thread(lsChild, xls1);
    call lsChild := Allocate();
    assume (lsChild != None());
    yield;
    async call thread(lsChild, xls2);
    yield;
}

procedure {:yields} {:phase 1} thread({:linear_in "tid"} tidls': [X]bool, {:linear_in "x"} xls': [X]bool)
requires {:phase 1} tidls' != None() && xls' != None();
{
    var {:linear "x"} xls: [X]bool;
    var {:linear "tid"} tidls: [X]bool;

    tidls := tidls';
    xls := xls';

    yield;
    call Lock(tidls);
    yield;
    assert {:phase 1} tidls != None() && xls != None();
    call Set(0);
    yield;
    assert {:phase 1} tidls != None() && xls != None();
    assert {:phase 1} x == 0;
    assert {:phase 1} tidls != None() && xls != None();
    call Unlock();
    yield;
}
