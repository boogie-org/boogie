// RUN: %boogie -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Tid;
type {:datatype} OptionTid;
function {:constructor} None(): OptionTid;
function {:constructor} Some(tid: Tid): OptionTid;

var {:layer 0, 1} b: bool;
var {:layer 0, 3} count: int;
var {:layer 1, 2} l: OptionTid;

function LockInv(b: bool, l: OptionTid): bool
{
    b <==> (l != None())
}
procedure {:yield_invariant} {:layer 1} YieldLockInv();
requires LockInv(b, l);

procedure {:yield_invariant} {:layer 2} Yield();

procedure {:atomic} {:layer 3,3} IncrSpec()
modifies count;
{
    count := count + 1;
}
procedure {:yields} {:layer 2} {:refines "IncrSpec"} Incr({:layer 1,2} {:hide} {:linear "tid"} tid: Tid)
requires {:layer 1} LockInv(b, l);
ensures {:layer 1} LockInv(b, l);
{
    var t: int;

    par YieldLockInv() | Yield();
    call Acquire(tid);
    par t := Read(tid) | YieldLockInv();
    par Write(tid, t+1) | YieldLockInv();
    call Release(tid);
    par YieldLockInv() | Yield();
}

procedure {:right} {:layer 2,2} AcquireSpec({:linear "tid"} tid: Tid)
modifies l;
{
    assume l == None();
    l := Some(tid);
}
procedure {:yields} {:layer 1} {:refines "AcquireSpec"} Acquire({:layer 1} {:linear "tid"} tid: Tid)
requires {:layer 1} LockInv(b, l);
ensures {:layer 1} LockInv(b, l);
{
    var t: bool;

    call YieldLockInv();
    call t := CAS(false, true);
    if (t) {
        call set_l(Some(tid));
        call YieldLockInv();
    } else {
        call {:mark} Acquire(tid);
    }
}

procedure {:left} {:layer 2,2} ReleaseSpec({:linear "tid"} tid: Tid)
modifies l;
{
    assert l == Some(tid);
    l := None();
}
procedure {:yields} {:layer 1} {:refines "ReleaseSpec"} Release({:layer 1} {:linear "tid"} tid: Tid)
requires {:layer 1} LockInv(b, l);
ensures {:layer 1} LockInv(b, l);
{
    var t: bool;

    call YieldLockInv();
    call t := CAS(true, false);
    call set_l(None());
    call YieldLockInv();
}

procedure {:both} {:layer 2,2} ReadSpec({:linear "tid"} tid: Tid) returns (v: int)
{
    assert l == Some(tid);
    v := count;
}
procedure {:yields} {:layer 1} {:refines "ReadSpec"} Read({:layer 1} {:linear "tid"} tid: Tid) returns (v: int)
{
    yield;
    call v := READ();
    yield;
}

procedure {:both} {:layer 2,2} WriteSpec({:linear "tid"} tid: Tid, v: int)
modifies count;
{
    assert l == Some(tid);
    count := v;
}
procedure {:yields} {:layer 1} {:refines "WriteSpec"} Write({:layer 1} {:linear "tid"} tid: Tid, v: int)
{
    yield;
    call WRITE(v);
    yield;
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

procedure {:inline} {:intro} {:layer 1} set_l(v: OptionTid)
modifies l;
{
    l := v;
}

function {:builtin "MapConst"} MapConstBool(bool): [Tid]bool;
function {:builtin "MapOr"} MapOr([Tid]bool, [Tid]bool) : [Tid]bool;

function {:inline} {:linear "tid"} TidCollector(x: Tid) : [Tid]bool
{
  MapConstBool(false)[x := true]
}
function {:inline} {:linear "tid"} TidSetCollector(x: [Tid]bool) : [Tid]bool
{
  x
}
