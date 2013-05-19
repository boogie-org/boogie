var a:[int]int;

procedure Allocate() returns ({:linear "tid"} xls: int);

procedure {:entrypoint} main() 
{
    var {:linear "tid"} i: int;
    var {:linear "tid"} j: int;
    call i := Allocate();
    call j := Allocate();
    call i := t(i) | j := Yield(j);
    call i := u(i) | j := u(j);
}

procedure t({:linear "tid"} i': int) returns ({:linear "tid"} i: int)
{
    i := i';

    a[i] := 42;
    call i := Yield(i);
    assert a[i] == 42;
}

procedure u({:linear "tid"} i': int) returns ({:linear "tid"} i: int) 
{
    i := i';

    a[i] := 42;
    yield;
    assert a[i] == 42;
}

procedure Yield({:linear "tid"} i': int) returns ({:linear "tid"} i: int)
ensures i == i';
ensures old(a)[i] == a[i];
{
    i := i';
    yield;
    assert old(a)[i] == a[i];
}