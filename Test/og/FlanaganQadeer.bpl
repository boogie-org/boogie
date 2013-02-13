type X;

const nil: X;
var l: X;
var x: int;

procedure {:entrypoint} main()
{
    var {:linear "tid"} tid: X;
    var val: int;

    while (*) 
    {
        havoc tid, val;
	assume tid != nil;
        call {:async} foo(tid, val);
    }
}

procedure foo({:linear "tid"} tid': X, val: int)
requires tid' != nil;
{
    var {:linear "tid"} tid: X;
    assume tid == tid';
    
    assume l == nil;
    l := tid;
    call tid := Yield(tid);
    x := val;
    call tid := Yield(tid);
    assert x == val;
    call tid := Yield(tid);
    l := nil;
}

procedure Yield({:linear "tid"} tid': X) returns ({:linear "tid"} tid: X)
requires tid' != nil;
ensures tid == tid';
ensures old(l) == tid ==> old(l) == l && old(x) == x;
{
    assume tid == tid';
    assert {:yield} tid != nil;
    assert (old(l) == tid ==> old(l) == l && old(x) == x);
}