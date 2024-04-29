// RUN: %parallel-boogie /lib:base "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Tid;

var {:layer 0, 1} b: bool;
var {:layer 0, 3} count: int;
var {:layer 1, 2} l: Option Tid;

yield invariant {:layer 1} LockInv();
invariant b <==> (l != None());

atomic action {:layer 3,3} IncrSpec()
modifies count;
{
    count := count + 1;
}
yield procedure {:layer 2} Incr({:layer 1,2} {:hide} {:linear} tid: One Tid)
refines IncrSpec;
preserves call LockInv();
{
    var t: int;

    call Acquire(tid);
    par t := Read(tid) | LockInv();
    par Write(tid, t+1) | LockInv();
    call Release(tid);
}

right action {:layer 2,2} AcquireSpec({:linear} tid: One Tid)
modifies l;
{
    assume l == None();
    l := Some(tid->val);
}
yield procedure {:layer 1} Acquire({:layer 1} {:linear} tid: One Tid)
refines AcquireSpec;
preserves call LockInv();
{
    var t: bool;

    call t := CAS(false, true);
    if (t) {
        call {:layer 1} l := Copy(Some(tid->val));
    } else {
        call {:mark} Acquire(tid);
    }
}

left action {:layer 2,2} ReleaseSpec({:linear} tid: One Tid)
modifies l;
{
    assert l == Some(tid->val);
    l := None();
}
yield procedure {:layer 1} Release({:layer 1} {:linear} tid: One Tid)
refines ReleaseSpec;
preserves call LockInv();
{
    var t: bool;

    call t := CAS(true, false);
    call {:layer 1} l := Copy(None());
}

both action {:layer 2,2} ReadSpec({:linear} tid: One Tid) returns (v: int)
{
    assert l == Some(tid->val);
    v := count;
}
yield procedure {:layer 1} Read({:layer 1} {:linear} tid: One Tid) returns (v: int)
refines ReadSpec;
{
    call v := READ();
}

both action {:layer 2,2} WriteSpec({:linear} tid: One Tid, v: int)
modifies count;
{
    assert l == Some(tid->val);
    count := v;
}
yield procedure {:layer 1} Write({:layer 1} {:linear} tid: One Tid, v: int)
refines WriteSpec;
{
    call WRITE(v);
}

atomic action {:layer 1,1} atomic_CAS(old_b: bool, new_b: bool) returns (success: bool)
modifies b;
{
    success := b == old_b;
    if (success) {
        b := new_b;
    }
}
yield procedure {:layer 0} CAS(old_b: bool, new_b: bool) returns (success: bool);
refines atomic_CAS;

atomic action {:layer 1,1} atomic_READ() returns (v: int)
{
    v := count;
}
yield procedure {:layer 0} READ() returns (v: int);
refines atomic_READ;

atomic action {:layer 1,1} atomic_WRITE(v: int)
modifies count;
{
    count := v;
}
yield procedure {:layer 0} WRITE(v: int);
refines atomic_WRITE;
