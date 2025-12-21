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
var {:layer 1,2} {:linear} usersInDriver: Set (One Perm);
var {:layer 0,1} pendingIo: int;
var {:layer 0,1} stoppingEvent: bool;

yield invariant {:layer 2} Inv2();
preserves stopped ==> stoppingFlag;

yield invariant {:layer 1} Inv1();
preserves stoppingEvent ==> stoppingFlag && usersInDriver->val == MapConst(false);
preserves pendingIo == Set_Size(usersInDriver) + (if stoppingFlag then 0 else 1);

function {:inline} Split(i: int, l: Set (One Perm), r: Set (One Perm)): bool
{
    l == Set_Singleton(One(Left(i))) && r == Set_Singleton(One(Right(i)))
}

// user code

yield procedure {:layer 2}
User(i: int, {:layer 1,2} {:linear} l: Set (One Perm), {:linear} {:layer 1,2} r: Set (One Perm))
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

atomic action {:layer 2} AtomicEnter#1(i: int, {:linear_in} l: Set (One Perm), {:linear} r: Set (One Perm))
modifies usersInDriver;
{
    assume !stoppingFlag;
    call Set_Put(usersInDriver, l);
}
yield procedure {:layer 1}
Enter#1(i: int, {:layer 1} {:linear_in} l: Set (One Perm), {:layer 1} {:linear} r: Set (One Perm))
refines AtomicEnter#1;
preserves call Inv1();
requires {:layer 1} Split(i, l, r);
{
    call Enter();
    call {:layer 1} usersInDriver := A(usersInDriver, l);
}

pure action A({:linear_in} usersInDriver: Set (One Perm), {:linear_in} l: Set (One Perm))
  returns ({:linear} usersInDriver': Set (One Perm))
{
    usersInDriver' := usersInDriver;
    call Set_Put(usersInDriver', l);
}

left action {:layer 2} AtomicCheckAssert#1(i: int, {:linear} r: Set (One Perm))
{
    assert r == Set_Singleton(One(Right(i))) && Set_Contains(usersInDriver, One(Left(i)));
    assert !stopped;
}
yield procedure {:layer 1}
CheckAssert#1(i: int, {:layer 1} {:linear} r: Set (One Perm))
refines AtomicCheckAssert#1;
preserves call Inv1();
{
    call CheckAssert();
}

left action {:layer 2} AtomicExit(i: int, {:linear_out} l: Set (One Perm), {:linear} r: Set (One Perm))
modifies usersInDriver;
{
    assert Split(i, l, r);
    call Set_Get(usersInDriver, l);
}
yield procedure {:layer 1}
Exit(i: int, {:layer 1} {:linear_out} l: Set (One Perm), {:layer 1} {:linear} r: Set (One Perm))
refines AtomicExit;
requires {:layer 1} Split(i, l, r);
preserves call Inv1();
{
    call DeleteReference();
    call {:layer 1} usersInDriver := B(usersInDriver, l);
    call {:layer 1} Lemma_SetSize_Subset(Set_Empty(), usersInDriver);
}

pure action B({:linear_in} usersInDriver: Set (One Perm), {:linear_out} l: Set (One Perm))
  returns ({:linear} usersInDriver': Set (One Perm))
{
    assert Set_IsSubset(l, usersInDriver);
    usersInDriver' := usersInDriver;
    call Set_Get(usersInDriver', l);
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
    call {:layer 1} Lemma_SetSize_Subset(Set_Empty(), usersInDriver);
}

atomic action {:layer 2} AtomicWaitAndStop()
modifies stopped;
{
    assume usersInDriver->val == MapConst(false);
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
