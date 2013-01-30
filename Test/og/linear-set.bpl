function {:inline} Subset(a: [X]bool, b: [X]bool) : bool
{
    MapImp(a, b) == MapConstBool(true)
}

function {:inline} In(a: X, b: [X]bool) : bool
{
    b[a]
}

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

procedure {:entrypoint} main({:linear "tid"} tidls': [X]bool, {:linear "x"} xls': [X]bool) 
requires tidls' != None() && xls' == All();
{
    var {:linear "tid"} tidls: [X]bool;
    var {:linear "x"} xls: [X]bool;
    var {:linear "tid"} lsChild: [X]bool;
    var {:linear "x"} xls1: [X]bool;
    var {:linear "x"} xls2: [X]bool;

    havoc tidls, xls;
    assume tidls' == tidls && xls' == xls;

    x := 42;
    assert {:yield} xls == All();
    assert x == 42;
    call xls1, xls2 := Split(xls);
    havoc lsChild;
    assume (lsChild != None());
    call {:async} thread(lsChild, xls1);
    havoc lsChild;
    assume (lsChild != None());
    call {:async} thread(lsChild, xls2);
}

procedure thread({:linear "tid"} tidls': [X]bool, {:linear "x"} xls': [X]bool)
requires tidls' != None() && xls' != None();
{
    var {:linear "x"} xls: [X]bool;
    var {:linear "tid"} tidls: [X]bool;

    havoc tidls, xls;
    assume tidls' == tidls && xls' == xls;

    assume l == None();
    l := tidls;
    assert {:yield} tidls != None() && xls != None();
    x := 0;
    assert {:yield} tidls != None() && xls != None();
    assert x == 0;
    assert {:yield} tidls != None() && xls != None();
    l := None();
}
