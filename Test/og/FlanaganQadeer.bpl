type X;

const nil: X;
var l: X;
var x: int;

procedure Allocate() returns ({:linear "tid"} xls: X);
ensures xls != nil;

procedure {:entrypoint} {:yields} main()
{
    var {:linear "tid"} tid: X;
    var val: int;

    while (*) 
    {
        call tid := Allocate();
        havoc val;
        async call foo(tid, val);
    }
}

procedure {:yields} {:stable} foo({:linear "tid"} tid': X, val: int)
requires tid' != nil;
{
    var {:linear "tid"} tid: X;
    tid := tid';
    
    assume l == nil;
    l := tid;
    call tid := Yield(tid);
    x := val;
    call tid := Yield(tid);
    assert x == val;
    call tid := Yield(tid);
    l := nil;
}

procedure {:yields} Yield({:linear "tid"} tid': X) returns ({:linear "tid"} tid: X)
requires tid' != nil;
ensures tid == tid';
ensures old(l) == tid ==> old(l) == l && old(x) == x;
{
    tid := tid';
    yield;
    assert tid != nil;
    assert (old(l) == tid ==> old(l) == l && old(x) == x);
}