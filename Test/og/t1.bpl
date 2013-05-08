function {:builtin "MapConst"} mapconstbool(bool) : [int]bool;

var g: int;
var h: int;

procedure A({:linear "tid"} tid_in: int) returns ({:linear "tid"} tid_out: int) 
{
    var {:linear "1"} x: [int]bool;
    var {:linear "2"} y: [int]bool;
    var {:linear "tid"} tid_child: int;
    assume tid_in == tid_out;    
    assume x == mapconstbool(true);
    assume y == mapconstbool(true);

    g := 0;
    yield;
    assert x == mapconstbool(true);    
    assert g == 0;    

    yield;
    assume tid_child != 0;
    async call B(tid_child, x);

    yield;
    assert x == mapconstbool(true);    
    assert g == 0;

    yield;
    h := 0;

    yield;
    assert h == 0 && y == mapconstbool(true);    

    yield;
    async call C(tid_child, y);
}

procedure B({:linear "tid"} tid_in: int, {:linear "1"} x_in: [int]bool) 
requires x_in != mapconstbool(false);
{
    var {:linear "tid"} tid_out: int;
    var {:linear "1"} x: [int]bool;
    assume tid_in == tid_out;
    assume x_in == x;    

    g := 1;
}

procedure C({:linear "tid"} tid_in: int, {:linear "2"} y_in: [int]bool) 
requires y_in != mapconstbool(false);
{
    var {:linear "tid"} tid_out: int;
    var {:linear "2"} y: [int]bool;
    assume tid_in == tid_out;
    assume y_in == y;    

    h := 1;
}
