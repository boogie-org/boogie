function {:builtin "MapConst"} mapconstbool(bool) : [int]bool;

procedure Allocate() returns ({:linear "tid"} xls: int);
ensures xls != 0;

procedure Allocate_1() returns ({:linear "1"} xls: [int]bool);
ensures xls == mapconstbool(true);

procedure Allocate_2() returns ({:linear "2"} xls: [int]bool);
ensures xls == mapconstbool(true);

var g: int;
var h: int;

procedure {:yields} A({:linear "tid"} tid_in: int) returns ({:linear "tid"} tid_out: int) 
{
    var {:linear "1"} x: [int]bool;
    var {:linear "2"} y: [int]bool;
    var {:linear "tid"} tid_child: int;
    tid_out := tid_in;    
    call x := Allocate_1();
    call y := Allocate_2();

    g := 0;
    yield;
    assert g == 0 && x == mapconstbool(true);    

    yield;
    call tid_child := Allocate();
    async call B(tid_child, x);

    yield;
    h := 0;

    yield;
    assert h == 0 && y == mapconstbool(true);    

    yield;
    call tid_child := Allocate();
    async call C(tid_child, y);
}

procedure {:yields} {:stable} B({:linear "tid"} tid_in: int, {:linear "1"} x_in: [int]bool) 
requires x_in != mapconstbool(false);
{
    var {:linear "tid"} tid_out: int;
    var {:linear "1"} x: [int]bool;
    tid_out := tid_in;
    x := x_in;    

    g := 1;

    yield;

    g := 2;
}

procedure {:yields} {:stable} C({:linear "tid"} tid_in: int, {:linear "2"} y_in: [int]bool) 
requires y_in != mapconstbool(false);
{
    var {:linear "tid"} tid_out: int;
    var {:linear "2"} y: [int]bool;
    tid_out := tid_in;
    y := y_in;    

    h := 1;

    yield;

    h := 2;
}