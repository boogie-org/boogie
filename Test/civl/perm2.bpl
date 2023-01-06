// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "tid", "1", "2"} IntTid = int;

var {:layer 0,1} g: int;
var {:layer 0,1} h: int;
var {:layer 0,1}{:linear "tid"} unallocated:[int]bool;

procedure {:atomic} {:layer 1} AtomicSetG(val:int)
modifies g;
{g := val; }

procedure {:yields} {:layer 0} {:refines "AtomicSetG"} SetG(val:int);

procedure {:atomic} {:layer 1} AtomicSetH(val:int)
modifies h;
{ h := val; }

procedure {:yields} {:layer 0} {:refines "AtomicSetH"} SetH(val:int);

procedure {:yields} {:layer 1} Allocate() returns ({:linear "tid"} xl: int)
ensures {:layer 1} xl != 0;
{
    call xl := AllocateLow();
}

procedure {:atomic} {:layer 1} AtomicAllocateLow() returns ({:linear "tid"} xls: int)
modifies unallocated;
{ assume xls != 0; assume unallocated[xls]; unallocated[xls] := false; }

procedure {:yields} {:layer 0} {:refines "AtomicAllocateLow"} AllocateLow() returns ({:linear "tid"} xls: int);

procedure {:yields} {:layer 1} A({:linear_in "tid"} tid_in: int, {:linear_in "1"} x: [int]bool, {:linear_in "2"} y: [int]bool) returns ({:linear "tid"} tid_out: int)
requires {:layer 1} x == MapConst(true);
requires {:layer 1} y == MapConst(true);
{
    var {:linear "tid"} tid_child: int;
    tid_out := tid_in;

    call SetG(0);
    yield;
    assert {:layer 1} g == 0 && x == MapConst(true);

    yield;
    call tid_child := Allocate();
    async call B(tid_child, x);

    yield;
    call SetH(0);

    yield;
    assert {:layer 1} h == 0 && y == MapConst(true);

    yield;
    call tid_child := Allocate();
    async call C(tid_child, y);

}

procedure {:yields} {:layer 1} B({:linear_in "tid"} tid_in: int, {:linear_in "1"} x_in: [int]bool)
requires {:layer 1} x_in != MapConst(false);
{
    var {:linear "tid"} tid_out: int;
    var {:linear "1"} x: [int]bool;
    tid_out := tid_in;
    x := x_in;

    call SetG(1);

    yield;

    call SetG(2);
}

procedure {:yields} {:layer 1} C({:linear_in "tid"} tid_in: int, {:linear_in "2"} y_in: [int]bool)
requires {:layer 1} y_in != MapConst(false);
{
    var {:linear "tid"} tid_out: int;
    var {:linear "2"} y: [int]bool;
    tid_out := tid_in;
    y := y_in;

    call SetH(1);

    yield;

    call SetH(2);
}
