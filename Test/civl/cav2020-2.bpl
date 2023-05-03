// RUN: %parallel-boogie /lib:base "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "tid"} Tid;

var {:layer 0, 1} b: bool;
var {:layer 0, 3} count: int;
var {:layer 1, 2} l: Option Tid;

yield invariant {:layer 1} LockInv();
invariant b <==> (l != None());

>-< action {:layer 3,3} IncrSpec()
modifies count;
{
    count := count + 1;
}
yield procedure {:layer 2} Incr({:layer 1,2} {:hide} {:linear "tid"} tid: Tid)
refines IncrSpec;
preserves call LockInv();
{
    var t: int;

    call Acquire(tid);
    par t := Read(tid) | LockInv();
    par Write(tid, t+1) | LockInv();
    call Release(tid);
}

-> action {:layer 2,2} AcquireSpec({:linear "tid"} tid: Tid)
modifies l;
{
    assume l == None();
    l := Some(tid);
}
yield procedure {:layer 1} Acquire({:layer 1} {:linear "tid"} tid: Tid)
refines AcquireSpec;
preserves call LockInv();
{
    var t: bool;

    call t := CAS(false, true);
    if (t) {
        call set_l(Some(tid));
    } else {
        call {:mark} Acquire(tid);
    }
}

<- action {:layer 2,2} ReleaseSpec({:linear "tid"} tid: Tid)
modifies l;
{
    assert l == Some(tid);
    l := None();
}
yield procedure {:layer 1} Release({:layer 1} {:linear "tid"} tid: Tid)
refines ReleaseSpec;
preserves call LockInv();
{
    var t: bool;

    call t := CAS(true, false);
    call set_l(None());
}

<-> action {:layer 2,2} ReadSpec({:linear "tid"} tid: Tid) returns (v: int)
{
    assert l == Some(tid);
    v := count;
}
yield procedure {:layer 1} Read({:layer 1} {:linear "tid"} tid: Tid) returns (v: int)
refines ReadSpec;
{
    call v := READ();
}

<-> action {:layer 2,2} WriteSpec({:linear "tid"} tid: Tid, v: int)
modifies count;
{
    assert l == Some(tid);
    count := v;
}
yield procedure {:layer 1} Write({:layer 1} {:linear "tid"} tid: Tid, v: int)
refines WriteSpec;
{
    call WRITE(v);
}

>-< action {:layer 1,1} atomic_CAS(old_b: bool, new_b: bool) returns (success: bool)
modifies b;
{
    success := b == old_b;
    if (success) {
        b := new_b;
    }
}
yield procedure {:layer 0} CAS(old_b: bool, new_b: bool) returns (success: bool);
refines atomic_CAS;

>-< action {:layer 1,1} atomic_READ() returns (v: int)
{
    v := count;
}
yield procedure {:layer 0} READ() returns (v: int);
refines atomic_READ;

>-< action {:layer 1,1} atomic_WRITE(v: int)
modifies count;
{
    count := v;
}
yield procedure {:layer 0} WRITE(v: int);
refines atomic_WRITE;

action {:layer 1} set_l(v: Option Tid)
modifies l;
{
    l := v;
}
