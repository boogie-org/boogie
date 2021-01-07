// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "tid"} Tid;
type {:datatype} Option _;
function {:constructor} None<T>(): Option T;
function {:constructor} Some<T>(t: T): Option T;

var {:layer 0, 1} b: bool;
var {:layer 0, 3} count: int;
var {:layer 1, 2} l: Option Tid;

procedure {:yield_invariant} {:layer 1} LockInv();
requires b <==> (l != None());

procedure {:atomic} {:layer 3,3} IncrSpec()
modifies count;
{
    count := count + 1;
}
procedure {:yields} {:layer 2} {:refines "IncrSpec"}
{:yield_preserves "LockInv"}
Incr({:layer 1,2} {:hide} {:linear "tid"} tid: Tid)
{
    var t: int;

    call Acquire(tid);
    par t := Read(tid) | LockInv();
    par Write(tid, t+1) | LockInv();
    call Release(tid);
}

procedure {:right} {:layer 2,2} AcquireSpec({:linear "tid"} tid: Tid)
modifies l;
{
    assume l == None();
    l := Some(tid);
}
procedure {:yields} {:layer 1} {:refines "AcquireSpec"}
{:yield_preserves "LockInv"}
Acquire({:layer 1} {:linear "tid"} tid: Tid)
{
    var t: bool;

    call t := CAS(false, true);
    if (t) {
        call set_l(Some(tid));
    } else {
        call {:refines} Acquire(tid);
    }
}

procedure {:left} {:layer 2,2} ReleaseSpec({:linear "tid"} tid: Tid)
modifies l;
{
    assert l == Some(tid);
    l := None();
}
procedure {:yields} {:layer 1} {:refines "ReleaseSpec"}
{:yield_preserves "LockInv"}
Release({:layer 1} {:linear "tid"} tid: Tid)
{
    var t: bool;

    call t := CAS(true, false);
    call set_l(None());
}

procedure {:both} {:layer 2,2} ReadSpec({:linear "tid"} tid: Tid) returns (v: int)
{
    assert l == Some(tid);
    v := count;
}
procedure {:yields} {:layer 1} {:refines "ReadSpec"} Read({:layer 1} {:linear "tid"} tid: Tid) returns (v: int)
{
    call v := READ();
}

procedure {:both} {:layer 2,2} WriteSpec({:linear "tid"} tid: Tid, v: int)
modifies count;
{
    assert l == Some(tid);
    count := v;
}
procedure {:yields} {:layer 1} {:refines "WriteSpec"} Write({:layer 1} {:linear "tid"} tid: Tid, v: int)
{
    call WRITE(v);
}

procedure {:atomic} {:layer 1,1} atomic_CAS(old_b: bool, new_b: bool) returns (success: bool)
modifies b;
{
    success := b == old_b;
    if (success) {
        b := new_b;
    }
}
procedure {:yields} {:layer 0} {:refines "atomic_CAS"} CAS(old_b: bool, new_b: bool) returns (success: bool);

procedure {:atomic} {:layer 1,1} atomic_READ() returns (v: int)
{
    v := count;
}
procedure {:yields} {:layer 0} {:refines "atomic_READ"} READ() returns (v: int);

procedure {:atomic} {:layer 1,1} atomic_WRITE(v: int)
modifies count;
{
    count := v;
}
procedure {:yields} {:layer 0} {:refines "atomic_WRITE"} WRITE(v: int);

procedure {:inline} {:intro} {:layer 1} set_l(v: Option Tid)
modifies l;
{
    l := v;
}
