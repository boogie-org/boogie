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

var x: int;
var l: [X]bool;

procedure Split({:linear "x"} xls: [X]bool) returns ({:linear "x"} xls1: [X]bool, {:linear "x"} xls2: [X]bool);
ensures xls == MapOr(xls1, xls2) && xls1 != None() && xls2 != None();

procedure Allocate() returns ({:linear "tid"} xls: [X]bool);

procedure {:entrypoint} main({:linear "tid"} tidls': [X]bool, {:linear "x"} xls': [X]bool) 
requires tidls' != None() && xls' == All();
{
    var {:linear "tid"} tidls: [X]bool;
    var {:linear "x"} xls: [X]bool;
    var {:linear "tid"} lsChild: [X]bool;
    var {:linear "x"} xls1: [X]bool;
    var {:linear "x"} xls2: [X]bool;

    tidls := tidls';
    xls := xls';

    x := 42;
    yield;
    assert xls == All();
    assert x == 42;
    call xls1, xls2 := Split(xls);
    call lsChild := Allocate();
    assume (lsChild != None());
    async call thread(lsChild, xls1);
    call lsChild := Allocate();
    assume (lsChild != None());
    async call thread(lsChild, xls2);
}

procedure thread({:linear "tid"} tidls': [X]bool, {:linear "x"} xls': [X]bool)
requires tidls' != None() && xls' != None();
{
    var {:linear "x"} xls: [X]bool;
    var {:linear "tid"} tidls: [X]bool;

    tidls := tidls';
    xls := xls';

    assume l == None();
    l := tidls;
    yield;
    assert tidls != None() && xls != None();
    x := 0;
    yield;
    assert tidls != None() && xls != None();
    assert x == 0;
    yield;
    assert tidls != None() && xls != None();
    l := None();
}
