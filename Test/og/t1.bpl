// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function {:builtin "MapConst"} mapconstbool(bool) : [int]bool;

function {:builtin "MapConst"} MapConstBool(bool) : [int]bool;
function {:inline} {:linear "tid"} TidCollector(x: int) : [int]bool
{
  MapConstBool(false)[x := true]
}

function {:inline} {:linear "1"} SetCollector1(x: [int]bool) : [int]bool
{
  x
}

function {:inline} {:linear "2"} SetCollector2(x: [int]bool) : [int]bool
{
  x
}

procedure Allocate() returns ({:linear "tid"} xls: int);
ensures {:phase 1} xls != 0;

procedure Allocate_1() returns ({:linear "1"} xls: [int]bool);
ensures {:phase 1} xls == mapconstbool(true);

procedure Allocate_2() returns ({:linear "2"} xls: [int]bool);
ensures {:phase 1} xls == mapconstbool(true);

var {:phase 1} g: int;
var {:phase 1} h: int;

procedure {:yields} {:phase 0,1} SetG(val:int);
ensures {:atomic} |{A: g := val; return true; }|;

procedure {:yields} {:phase 0,1} SetH(val:int);
ensures {:atomic} |{A: h := val; return true; }|;

procedure {:yields} {:phase 1} A({:linear "tid"} tid_in: int) returns ({:linear "tid"} tid_out: int) 
{
    var {:linear "1"} x: [int]bool;
    var {:linear "2"} y: [int]bool;
    var {:linear "tid"} tid_child: int;
    tid_out := tid_in;
    call x := Allocate_1();
    call y := Allocate_2();

    yield;
    call SetG(0);
    yield;
    assert {:phase 1} x == mapconstbool(true);    
    assert {:phase 1} g == 0;    

    yield;
    call tid_child := Allocate();
    async call B(tid_child, x);

    yield;
    assert {:phase 1} x == mapconstbool(true);    
    assert {:phase 1} g == 0;

    yield;
    call SetH(0);

    yield;
    assert {:phase 1} h == 0 && y == mapconstbool(true);    

    yield;
    call tid_child := Allocate();
    async call C(tid_child, y);

    yield;
}

procedure {:yields} {:phase 1} B({:linear "tid"} tid_in: int, {:linear "1"} x_in: [int]bool) 
requires {:phase 1} x_in != mapconstbool(false);
{
    var {:linear "tid"} tid_out: int;
    var {:linear "1"} x: [int]bool;
    tid_out := tid_in;
    x := x_in;    

    yield;
    call SetG(1);
    yield;
}

procedure {:yields} {:phase 1} C({:linear "tid"} tid_in: int, {:linear "2"} y_in: [int]bool) 
requires {:phase 1} y_in != mapconstbool(false);
{
    var {:linear "tid"} tid_out: int;
    var {:linear "2"} y: [int]bool;
    tid_out := tid_in;
    y := y_in;   

    yield;
    call SetH(1);
    yield;
}
