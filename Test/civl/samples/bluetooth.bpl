// RUN: %parallel-boogie -lib:set_size "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*
This example is inspired by coordination seen in device drivers.
A stopping thread is attempting to clean up driver resources and
forces user threads to exit the driver and not re-enter. This proof
works for arbitrary number of user threads.

This example provides another instance of permission redistribution;
see cav2020-3.bpl for another example inspired by a concurrent
garbage collector.
*/

datatype Perm { Left(i: int), Right(i: int) }

var {:layer 0,3} stoppingFlag: bool;
var {:layer 0,2} stopped: bool;
var {:layer 1,2} {:linear} usersInDriver: UnitMap (One Perm);
var {:layer 0,1} pendingIo: int;
var {:layer 0,1} stoppingEvent: bool;

yield invariant {:layer 2} Inv2();
preserves stopped ==> stoppingFlag;

yield invariant {:layer 1} Inv1();
preserves stoppingEvent ==> stoppingFlag && usersInDriver->dom == MapConst(false);
preserves pendingIo == Set_Size(usersInDriver->dom) + (if stoppingFlag then 0 else 1);

function {:inline} Split(i: int, l: UnitMap (One Perm), r: UnitMap (One Perm)): bool
{
    l->dom == Set_Singleton(One(Left(i))) && r->dom == Set_Singleton(One(Right(i)))
}

// user code

yield procedure {:layer 2}
User(i: int, {:layer 1,2} {:linear} l: UnitMap (One Perm), {:linear} {:layer 1,2} r: UnitMap (One Perm))
preserves call Inv2();
preserves call Inv1();
requires {:layer 1, 2} Split(i, l, r);
{
    while (*)
    invariant {:yields} true;
    invariant call Inv1();
    invariant call Inv2();
    {
        call Enter#1(i, l, r);
        call CheckAssert#1(i, r);
        call Exit(i, l, r);
    }
}

atomic action {:layer 2} AtomicEnter#1(i: int, {:linear_in} l: UnitMap (One Perm), {:linear} r: UnitMap (One Perm))
modifies usersInDriver;
{
    assume !stoppingFlag;
    call Map_Join(usersInDriver, l);
}
yield procedure {:layer 1}
Enter#1(i: int, {:layer 1} {:linear_in} l: UnitMap (One Perm), {:layer 1} {:linear} r: UnitMap (One Perm))
refines AtomicEnter#1;
preserves call Inv1();
requires {:layer 1} Split(i, l, r);
{
    call Enter();
    call {:layer 1} usersInDriver := A(usersInDriver, l);
}

pure action A({:linear_in} usersInDriver: UnitMap (One Perm), {:linear_in} l: UnitMap (One Perm))
  returns ({:linear} usersInDriver': UnitMap (One Perm))
{
    usersInDriver' := usersInDriver;
    call Map_Join(usersInDriver', l);
}

left action {:layer 2} AtomicCheckAssert#1(i: int, {:linear} r: UnitMap (One Perm))
{
    assert r->dom == Set_Singleton(One(Right(i))) && Map_Contains(usersInDriver, One(Left(i)));
    assert !stopped;
}
yield procedure {:layer 1}
CheckAssert#1(i: int, {:layer 1} {:linear} r: UnitMap (One Perm))
refines AtomicCheckAssert#1;
preserves call Inv1();
{
    call CheckAssert();
}

left action {:layer 2} AtomicExit(i: int, {:linear_out} l: UnitMap (One Perm), {:linear} r: UnitMap (One Perm))
modifies usersInDriver;
{
    var _l: UnitMap (One Perm);
    assert Split(i, l, r);
    call _l := Map_Split(usersInDriver, l->dom);
    call Move(_l, l);

}
yield procedure {:layer 1}
Exit(i: int, {:layer 1} {:linear_out} l: UnitMap (One Perm), {:layer 1} {:linear} r: UnitMap (One Perm))
refines AtomicExit;
requires {:layer 1} Split(i, l, r);
preserves call Inv1();
{
    call DeleteReference();
    call {:layer 1} usersInDriver := B(usersInDriver, l);
    call {:layer 1} Lemma_SetSize_Subset(Set_Empty(), usersInDriver->dom);
}

pure action B({:linear_in} usersInDriver: UnitMap (One Perm), {:linear_out} l: UnitMap (One Perm))
  returns ({:linear} usersInDriver': UnitMap (One Perm))
{
    var _l: UnitMap (One Perm);
    assert Set_IsSubset(l->dom, usersInDriver->dom);
    usersInDriver' := usersInDriver;
    call _l := Map_Split(usersInDriver', l->dom);
    call Move(_l, l);
}

// stopper code

yield procedure {:layer 2} Stopper({:linear} i: One int)
refines AtomicSetStoppingFlag;
preserves call Inv2();
preserves call Inv1();
{
    call Close(i);
    call WaitAndStop();
}

yield procedure {:layer 1} Close({:linear} i: One int)
refines AtomicSetStoppingFlag;
preserves call Inv1();
{
    call SetStoppingFlag(i);
    call DeleteReference();
    call {:layer 1} Lemma_SetSize_Subset(Set_Empty(), usersInDriver->dom);
}

atomic action {:layer 2} AtomicWaitAndStop()
modifies stopped;
{
    assume usersInDriver->dom == MapConst(false);
    stopped := true;
}
yield procedure {:layer 1} WaitAndStop()
refines AtomicWaitAndStop;
preserves call Inv1();
{
    call WaitOnStoppingEvent();
    call SetStopped();
}

/// primitive actions

atomic action {:layer 1} AtomicEnter()
modifies pendingIo;
{
    assume !stoppingFlag;
    pendingIo := pendingIo + 1;
}
yield procedure {:layer 0} Enter();
refines AtomicEnter;

atomic action {:layer 1} AtomicCheckAssert()
{
    assert !stopped;
}
yield procedure {:layer 0} CheckAssert();
refines AtomicCheckAssert;

right action {:layer 1,3} AtomicSetStoppingFlag({:linear} i: One int)
modifies stoppingFlag;
{
    // The first assertion ensures that there is at most one stopper.
    // Otherwise AtomicSetStoppingFlag does not commute with itself.
    assert i->val == 0;
    assert !stoppingFlag;
    stoppingFlag := true;
}
yield procedure {:layer 0} SetStoppingFlag({:linear} i: One int);
refines AtomicSetStoppingFlag;

atomic action {:layer 1} AtomicDeleteReference()
modifies pendingIo, stoppingEvent;
{
    pendingIo := pendingIo - 1;
    if (pendingIo == 0) {
        stoppingEvent := true;
    }
}
yield procedure {:layer 0} DeleteReference();
refines AtomicDeleteReference;

atomic action {:layer 1} AtomicWaitOnStoppingEvent()
{
    assume stoppingEvent;
}
yield procedure {:layer 0} WaitOnStoppingEvent();
refines AtomicWaitOnStoppingEvent;

left action {:layer 1} AtomicSetStopped()
modifies stopped;
{
    stopped := true;
}
yield procedure {:layer 0} SetStopped();
refines AtomicSetStopped;
