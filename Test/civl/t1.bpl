// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function {:builtin "MapConst"} mapconstbool(bool) : [int]bool;

function {:builtin "MapConst"} MapConstBool(bool) : [int]bool;
function {:inline} {:linear "tid"} TidCollector(x: int) : [int]bool
{
  MapConstBool(false)[x := true]
}
function {:inline} {:linear "tid"} TidSetCollector(x: [int]bool) : [int]bool
{
  x
}

function {:inline} {:linear "1"} SetCollector1(x: [int]bool) : [int]bool
{
  x
}

function {:inline} {:linear "2"} SetCollector2(x: [int]bool) : [int]bool
{
  x
}

var {:layer 0,1} g: int;
var {:layer 0,1} h: int;

var {:layer 0,1}{:linear "tid"} unallocated:[int]bool;

procedure {:atomic} {:layer 1} AtomicSetG(val:int)
modifies g;
{ g := val; }

procedure {:yields} {:layer 0} {:refines "AtomicSetG"} SetG(val:int);

procedure {:atomic} {:layer 1} AtomicSetH(val:int)
modifies h;
{ h := val; }

procedure {:yields} {:layer 0} {:refines "AtomicSetH"} SetH(val:int);

procedure {:yields} {:layer 1} Yield({:linear "1"} x: [int]bool)
requires {:layer 1} x == mapconstbool(true) && g == 0;
ensures {:layer 1} x == mapconstbool(true) && g == 0;
{
    yield;
    assert {:layer 1} x == mapconstbool(true) && g == 0;
}

procedure {:yields} {:layer 1} Allocate() returns ({:linear "tid"} xl: int)
ensures {:layer 1} xl != 0;
{
    yield;
    call xl := AllocateLow();
    yield;
}

procedure {:atomic} {:layer 1} AtomicAllocateLow() returns ({:linear "tid"} xls: int)
modifies unallocated;
{ assume xls != 0 && unallocated[xls]; unallocated[xls] := false; }

procedure {:yields} {:layer 0} {:refines "AtomicAllocateLow"} AllocateLow() returns ({:linear "tid"} xls: int);

procedure {:yields} {:layer 1} A({:linear_in "tid"} tid_in: int, {:linear_in "1"} x: [int]bool, {:linear_in "2"} y: [int]bool) returns ({:linear "tid"} tid_out: int)
requires {:layer 1} x == mapconstbool(true);
requires {:layer 1} y == mapconstbool(true);
{
    var {:linear "tid"} tid_child: int;
    tid_out := tid_in;

    yield;
    call SetG(0);

    par tid_child := Allocate() | Yield(x);

    async call B(tid_child, x);

    yield;
    assert {:layer 1} x == mapconstbool(true);
    assert {:layer 1} g == 0;

    call SetH(0);

    yield;
    assert {:layer 1} h == 0 && y == mapconstbool(true);

    yield;
    call tid_child := Allocate();
    async call C(tid_child, y);

    yield;
}

procedure {:yields} {:layer 1} B({:linear_in "tid"} tid_in: int, {:linear_in "1"} x_in: [int]bool)
requires {:layer 1} x_in != mapconstbool(false);
{
    var {:linear "tid"} tid_out: int;
    var {:linear "1"} x: [int]bool;
    tid_out := tid_in;
    x := x_in;

    yield;
    call SetG(1);
    yield;
}

procedure {:yields} {:layer 1} C({:linear_in "tid"} tid_in: int, {:linear_in "2"} y_in: [int]bool)
requires {:layer 1} y_in != mapconstbool(false);
{
    var {:linear "tid"} tid_out: int;
    var {:linear "2"} y: [int]bool;
    tid_out := tid_in;
    y := y_in;

    yield;
    call SetH(1);
    yield;
}
