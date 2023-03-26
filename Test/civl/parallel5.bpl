// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "tid"} X = int;

var {:layer 0,1} a:[int]int;

yield procedure {:layer 1} Allocate() returns ({:linear "tid"} tid: int);

action {:layer 1} AtomicWrite(idx: int, val: int)
modifies a;
{ a[idx] := val; }

yield procedure {:layer 0} Write(idx: int, val: int) refines AtomicWrite;

yield procedure {:layer 1} main()
{
    var {:linear "tid"} i: int;
    var {:linear "tid"} j: int;
    call i := Allocate();
    call j := Allocate();
    par i := t(i) | Yield(j, a);
    par i := u(i) | j := u(j);
}

yield procedure {:layer 1} t({:linear_in "tid"} i': int) returns ({:linear "tid"} i: int)
{
    i := i';

    call Write(i, 42);
    call Yield(i, a);
    assert {:layer 1} a[i] == 42;
}

yield procedure {:layer 1} u({:linear_in "tid"} i': int) returns ({:linear "tid"} i: int)
ensures call Yield_42(i, 42);
{
    i := i';

    call Write(i, 42);
}

yield invariant {:layer 1} Yield({:linear "tid"} i: int, old_a: [int]int);
invariant old_a[i] == a[i];

yield invariant {:layer 1} Yield_42({:linear "tid"} i: int, v: int);
invariant v == a[i];
