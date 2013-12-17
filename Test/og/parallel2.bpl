var a:[int]int;

procedure Allocate() returns ({:linear "tid"} xls: int);

procedure {:entrypoint} {:yields} main() 
{
    var {:linear "tid"} i: int;
    var {:linear "tid"} j: int;
    call i := Allocate();
    call j := Allocate();
    par i := t(i) | j := t(j);
    par i := u(i) | j := u(j);
}

procedure {:yields} {:stable} t({:linear "tid"} i': int) returns ({:linear "tid"} i: int)
{
    i := i';

    a[i] := 42;
    call i := Yield(i);
    assert a[i] == 42;
}

procedure {:yields} {:stable} u({:linear "tid"} i': int) returns ({:linear "tid"} i: int) 
{
    i := i';

    a[i] := 42;
    yield;
    assert a[i] == 42;
}

procedure {:yields} Yield({:linear "tid"} i': int) returns ({:linear "tid"} i: int)
ensures i == i';
ensures old(a)[i] == a[i];
{
    i := i';
    yield;
    assert old(a)[i] == a[i];
}