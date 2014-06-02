// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:phase 1} a:[int]int;

function {:builtin "MapConst"} MapConstBool(bool) : [int]bool;
function {:inline} {:linear "tid"} TidCollector(x: int) : [int]bool
{
  MapConstBool(false)[x := true]
}

procedure Allocate() returns ({:linear "tid"} xls: int);

procedure {:yields} {:phase 0,1} Write(idx: int, val: int);
ensures {:atomic} |{A: a[idx] := val; return true; }|;

procedure {:yields} {:phase 1} main() 
{
    var {:linear "tid"} i: int;
    var {:linear "tid"} j: int;
    call i := Allocate();
    call j := Allocate();
    par i := t(i) | j := t(j);
    par i := u(i) | j := u(j);
}

procedure {:yields} {:phase 1} t({:linear "tid"} i': int) returns ({:linear "tid"} i: int)
{
    i := i';

    yield;
    call Write(i, 42);
    call Yield(i);
    assert {:phase 1} a[i] == 42;
}

procedure {:yields} {:phase 1} u({:linear "tid"} i': int) returns ({:linear "tid"} i: int) 
{
    i := i';

    yield;
    call Write(i, 42);
    yield;
    assert {:phase 1} a[i] == 42;
}

procedure {:yields} {:phase 1} Yield({:cnst "tid"} i: int)
ensures {:phase 1} old(a)[i] == a[i];
{
    yield;
    assert {:phase 1} old(a)[i] == a[i];
}