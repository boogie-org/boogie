// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type X;
const nil: X;
var {:layer 0,1} l: X;
var {:layer 0,1} x: int;
var {:layer 0,1}{:linear "tid"} unallocated:[X]bool;

function {:builtin "MapConst"} MapConstBool(bool) : [X]bool;
function {:inline} {:linear "tid"} TidCollector(x: X) : [X]bool
{
  MapConstBool(false)[x := true]
}
function {:inline} {:linear "tid"} TidSetCollector(x: [X]bool) : [X]bool
{
  x
}

procedure {:yields} {:layer 1} Allocate() returns ({:linear "tid"} xl: X)
ensures {:layer 1} xl != nil;
{
    yield;
    call xl := AllocateLow();
    yield;
}

procedure {:yields} {:layer 1} main()
{
    var {:linear "tid"} tid: X;
    var val: int;

    yield;
    while (*)
    {
        call tid := Allocate();
        havoc val;
        async call foo(tid, val);
        yield;
    }
    yield;
}

procedure {:atomic} {:layer 1} AtomicLock(tid: X)
modifies l;
{ assume l == nil; l := tid; }

procedure {:yields} {:layer 0} {:refines "AtomicLock"} Lock(tid: X);

procedure {:atomic} {:layer 1} AtomicUnlock()
modifies l;
{ l := nil; }

procedure {:yields} {:layer 0} {:refines "AtomicUnlock"} Unlock();

procedure {:atomic} {:layer 1} AtomicSet(val: int)
modifies x;
{ x := val; }

procedure {:yields} {:layer 0} {:refines "AtomicSet"} Set(val: int);

procedure {:atomic} {:layer 1} AtomicAllocateLow() returns ({:linear "tid"} xl: X)
modifies unallocated;
{ assume xl != nil; assume unallocated[xl]; unallocated[xl] := false; }

procedure {:yields} {:layer 0} {:refines "AtomicAllocateLow"} AllocateLow() returns ({:linear "tid"} xl: X);

procedure {:yields} {:layer 1} foo({:linear_in "tid"} tid': X, val: int)
requires {:layer 1} tid' != nil;
{
    var {:linear "tid"} tid: X;
    tid := tid';

    yield;
    call Lock(tid);
    call tid := Yield(tid);
    call Set(val);
    call tid := Yield(tid);
    assert {:layer 1} x == val;
    call tid := Yield(tid);
    call Unlock();
    yield;
}

procedure {:yields} {:layer 1} Yield({:linear_in "tid"} tid': X) returns ({:linear "tid"} tid: X)
requires {:layer 1} tid' != nil;
ensures {:layer 1} tid == tid';
ensures {:layer 1} old(l) == tid ==> old(l) == l && old(x) == x;
{
    tid := tid';
    yield;
    assert {:layer 1} tid != nil;
    assert {:layer 1} (old(l) == tid ==> old(l) == l && old(x) == x);
}
