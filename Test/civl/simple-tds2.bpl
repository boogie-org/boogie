function {:builtin "MapConst"} MapConstBool(bool): [int]bool;
function {:inline} {:linear "tid"} TidCollector(x: int) : [int]bool
{
  MapConstBool(false)[x := true]
}

var {:layer 0,5} x: [int]int;
const unique p: int;
const unique r: int;

const n: int;
axiom 0 <= n;

procedure {:yields} {:layer 0} {:refines "AtomicP0"} P0({:linear "tid"} tid: int);
procedure {:left} {:layer 1} AtomicP0({:linear "tid"} tid: int)
modifies x;
{
    var y: [int]int;
    assert tid == p;
    assert (forall i: int :: 0 <= i && i < n ==> x[i] == 0);
    assume (forall i: int :: 0 <= i && i < n ==> y[i] == 1);
    assume (forall i: int :: (0 <= i && i < n) || y[i] == x[i]);    
    x := y;
}

procedure {:yields} {:layer 0} {:refines "AtomicQ0"} Q0({:linear "tid"} tid: int);
procedure {:atomic} {:layer 1} AtomicQ0({:linear "tid"} tid: int)
modifies x;
{ assert 0 <= tid && tid < n; assume x[tid] == 1; x[tid] := 2; }

procedure {:yields} {:layer 0} {:refines "AtomicR0"} R0({:linear "tid"} tid: int);
procedure {:atomic} {:layer 1,3} AtomicR0({:linear "tid"} tid: int)
modifies x;
{
    var y: [int]int;
    assert tid == r;
    assume (forall i: int :: 0 <= i && i < n ==> x[i] == 2);
    assume (forall i: int :: 0 <= i && i < n ==> y[i] == 3);
    assume (forall i: int :: (0 <= i && i < n) || y[i] == x[i]);    
    x := y;
}

procedure {:yields} {:layer 1} {:refines "AtomicP1"} P1({:linear_in "tid"} tid: int) { yield; async call P0(tid); yield; }
procedure {:atomic} {:layer 2,3} AtomicP1({:linear_in "tid"} tid: int)
modifies x;
{
    var y: [int]int;
    assert tid == p;
    assert (forall i: int :: 0 <= i && i < n ==> x[i] == 0);
    assume (forall i: int :: 0 <= i && i < n ==> y[i] == 1);
    assume (forall i: int :: (0 <= i && i < n) || y[i] == x[i]);    
    x := y;
}

procedure {:yields} {:layer 1} {:refines "AtomicQ1"} Q1({:linear "tid"} tid: int) { yield; call Q0(tid); yield; }
procedure {:left} {:layer 2,3} AtomicQ1({:linear "tid"} tid: int)
modifies x;
{ assert 0 <= tid && tid < n; assert x[tid] == 1; x[tid] := 2; }

procedure {:yields} {:layer 3} {:refines "AtomicR3"} R3({:linear "tid"} tid: int) { yield; call R0(tid); yield; }
procedure {:left} {:layer 4} AtomicR3({:linear "tid"} tid: int)
modifies x;
{
    var y: [int]int;
    assert tid == r;
    assert (forall i: int :: 0 <= i && i < n ==> x[i] == 2);
    assume (forall i: int :: 0 <= i && i < n ==> y[i] == 3);
    assume (forall i: int :: (0 <= i && i < n) || y[i] == x[i]);    
    x := y;
}

procedure {:yields} {:layer 0} {:refines "AtomicAlloc"} Alloc(i: int, {:linear_in "tid"} tidq: [int]bool) returns ({:linear "tid"} id: int, {:linear "tid"} tidq':[int]bool);
procedure {:both} {:layer 1,5} AtomicAlloc(i: int, {:linear_in "tid"} tidq: [int]bool) returns ({:linear "tid"} id: int, {:linear "tid"} tidq':[int]bool)
{ assert tidq[i]; id := i; tidq' := tidq[i := false]; }

procedure {:layer 3} SnapshotX() returns (old_x: [int]int);
ensures x == old_x;

procedure {:yields} {:layer 3} {:refines "AtomicMain3"} Main3({:linear_in "tid"} tidp: int, {:linear_in "tid"} tidq: [int]bool) {
    var i: int;
    var {:linear "tid"} tidq': [int]bool;
    var {:linear "tid"} id: int;
    var {:layer 3} x_old: [int]int;
    yield;
    call P1(tidp);
    i := 0;
    tidq' := tidq;
    call x_old := SnapshotX();
    while (i < n)
    invariant {:terminates} {:layer 0, 1, 3} true;
    invariant {:layer 3} 0 <= i && i <= n;
    invariant {:layer 3} (forall j: int :: (i <= j && j < n) <==> tidq'[j]);
    invariant {:layer 3} (forall j: int :: (0 <= j && j < i) ==> x[j] == 2);    
    invariant {:layer 3} (forall j: int :: (i <= j && j < n) ==> x[j] == 1);
    invariant {:layer 3} (forall j: int :: (0 <= j && j < n) || x[j] == x_old[j]);
    {
        call id, tidq' := Alloc(i, tidq');
        async call Q1(id);
	i := i + 1;
    }
    yield;
}
procedure {:atomic} {:layer 4} AtomicMain3({:linear_in "tid"} tidp: int, {:linear_in "tid"} tidq: [int]bool)
modifies x;
{
    var y: [int]int;
    assert tidp == p;
    assert (forall i: int :: (0 <= i && i < n) <==> tidq[i]);
    assert (forall i: int :: 0 <= i && i < n ==> x[i] == 0);
    assume (forall i: int :: 0 <= i && i < n ==> y[i] == 2);
    assume (forall i: int :: (0 <= i && i < n) || y[i] == x[i]);    
    x := y;
}

procedure {:yields} {:layer 4} {:refines "AtomicMain4"} Main4({:linear_in "tid"} tidp: int, {:linear_in "tid"} tidq: [int]bool, {:linear_in "tid"} tidr: int) {
    yield;
    call Main3(tidp, tidq);
    async call R3(tidr);
    yield;
}
procedure {:atomic} {:layer 5} AtomicMain4({:linear_in "tid"} tidp: int, {:linear_in "tid"} tidq: [int]bool, {:linear_in "tid"} tidr: int)
modifies x;
{
    var y: [int]int;
    assert tidp == p && tidr == r;
    assert (forall i: int :: (0 <= i && i < n) <==> tidq[i]);
    assert (forall i: int :: 0 <= i && i < n ==> x[i] == 0);
    assume (forall i: int :: 0 <= i && i < n ==> y[i] == 3);
    assume (forall i: int :: (0 <= i && i < n) || y[i] == x[i]);    
    x := y;
}
