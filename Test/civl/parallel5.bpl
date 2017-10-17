// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,1} a:[int]int;

procedure {:yields} {:layer 1} Allocate() returns ({:linear "tid"} tid: int)
{
    yield;
    call tid := AllocateLow();
    yield;
}

function {:builtin "MapConst"} MapConstBool(bool) : [int]bool;
function {:inline} {:linear "tid"} TidCollector(x: int) : [int]bool
{
  MapConstBool(false)[x := true]
}

procedure {:atomic} {:layer 1} AtomicWrite(idx: int, val: int)
modifies a;
{ a[idx] := val; }

procedure {:yields} {:layer 0} {:refines "AtomicWrite"} Write(idx: int, val: int);

procedure {:yields} {:layer 1} main()
{
    var {:linear "tid"} i: int;
    var {:linear "tid"} j: int;
    call i := Allocate();
    call j := Allocate();
    par i := t(i) | Yield(j);
    par i := u(i) | j := u(j);
}

procedure {:yields} {:layer 1} t({:linear_in "tid"} i': int) returns ({:linear "tid"} i: int)
{
    i := i';

    yield;
    call Write(i, 42);
    call Yield(i);
    assert {:layer 1} a[i] == 42;
}

procedure {:yields} {:layer 1} u({:linear_in "tid"} i': int) returns ({:linear "tid"} i: int)
{
    i := i';

    yield;
    call Write(i, 42);
    yield;
    assert {:layer 1} a[i] == 42;
}

procedure {:yields} {:layer 1} Yield({:linear "tid"} i: int)
ensures {:layer 1} old(a)[i] == a[i];
{
    yield;
    assert {:layer 1} old(a)[i] == a[i];
}

procedure {:yields} {:layer 0} AllocateLow() returns ({:linear "tid"} tid: int);
