// RUN: %parallel-boogie "%s" > "%t"
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

function Size<T>(set: [T]bool): int;
axiom {:ctor "Lset"} (forall<T> set: [T]bool :: Size(set) >= 0);

pure procedure SizeLemma<T>(X: [T]bool, x: T);
ensures Size(X[x := false]) + 1 == Size(X[x := true]);

pure procedure SubsetSizeRelationLemma<T>(X: [T]bool, Y: [T]bool);
requires MapImp(X, Y) == MapConst(true);
ensures X == Y || Size(X) < Size(Y);

var {:layer 0,3} stoppingFlag: bool;
var {:layer 0,2} stopped: bool;
var {:layer 1,2} usersInDriver: Lset Perm;
var {:layer 0,1} pendingIo: int;
var {:layer 0,1} stoppingEvent: bool;

yield invariant {:layer 2} Inv2();
invariant stopped ==> stoppingFlag;

yield invariant {:layer 1} Inv1();
invariant stoppingEvent ==> stoppingFlag && usersInDriver->dom == MapConst(false);
invariant pendingIo == Size(usersInDriver->dom) + (if stoppingFlag then 0 else 1);

// user code

yield procedure {:layer 2}
User(i: int, {:layer 1,2} l: Lval Perm, {:layer 1,2} r: Lval Perm)
preserves call Inv2();
preserves call Inv1();
requires {:layer 1, 2} l->val == Left(i) && r->val == Right(i);
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

>-< action {:layer 2} AtomicEnter#1(i: int, {:linear_in} l: Lval Perm, r: Lval Perm)
modifies usersInDriver;
{
    assume !stoppingFlag;
    call AddToBarrier(i, l);
}
yield procedure {:layer 1}
Enter#1(i: int, {:layer 1} {:linear_in} l: Lval Perm, {:layer 1} r: Lval Perm)
refines AtomicEnter#1;
preserves call Inv1();
requires {:layer 1} l->val == Left(i) && r->val == Right(i);
{
    call Enter();
    call {:layer 1} SizeLemma(usersInDriver->dom, Left(i));
    call AddToBarrier(i, l);
}

<- action {:layer 2} AtomicCheckAssert#1(i: int, r: Lval Perm)
{
    assert r->val == Right(i) && usersInDriver->dom[Left(i)];
    assert !stopped;
}
yield procedure {:layer 1}
CheckAssert#1(i: int, {:layer 1} r: Lval Perm)
refines AtomicCheckAssert#1;
preserves call Inv1();
{
    call CheckAssert();
}

<- action {:layer 2} AtomicExit(i: int, {:linear_out} l: Lval Perm, r: Lval Perm)
modifies usersInDriver;
{
    assert l->val == Left(i) && r->val == Right(i);
    call RemoveFromBarrier(i, l);
}
yield procedure {:layer 1}
Exit(i: int, {:layer 1} {:linear_out} l: Lval Perm, {:layer 1} r: Lval Perm)
refines AtomicExit;
preserves call Inv1();
{
    call DeleteReference();
    call {:layer 1} SizeLemma(usersInDriver->dom, Left(i));
    call RemoveFromBarrier(i, l);
    call {:layer 1} SubsetSizeRelationLemma(MapConst(false), usersInDriver->dom);
}

// stopper code

yield procedure {:layer 2} Stopper(i: Lval int)
refines AtomicSetStoppingFlag;
preserves call Inv2();
preserves call Inv1();
{
    call Close(i);
    call WaitAndStop();
}

yield procedure {:layer 1} Close(i: Lval int)
refines AtomicSetStoppingFlag;
preserves call Inv1();
{
    call SetStoppingFlag(i);
    call DeleteReference();
    call {:layer 1} SubsetSizeRelationLemma(MapConst(false), usersInDriver->dom);
}

>-< action {:layer 2} AtomicWaitAndStop()
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

/// introduction actions

action {:layer 1, 2} AddToBarrier(i: int, {:linear_in} l: Lval Perm)
modifies usersInDriver;
{
    call Lval_Transfer(l, usersInDriver);
}

action {:layer 1, 2} RemoveFromBarrier(i: int, {:linear_out} l: Lval Perm)
modifies usersInDriver;
{
    call Lval_Split(l, usersInDriver);
}

/// primitive actions

>-< action {:layer 1} AtomicEnter()
modifies pendingIo;
{
    assume !stoppingFlag;
    pendingIo := pendingIo + 1;
}
yield procedure {:layer 0} Enter();
refines AtomicEnter;

>-< action {:layer 1} AtomicCheckAssert()
{
    assert !stopped;
}
yield procedure {:layer 0} CheckAssert();
refines AtomicCheckAssert;

-> action {:layer 1,3} AtomicSetStoppingFlag(i: Lval int)
modifies stoppingFlag;
{
    // The first assertion ensures that there is at most one stopper.
    // Otherwise AtomicSetStoppingFlag does not commute with itself.
    assert i->val == 0;
    assert !stoppingFlag;
    stoppingFlag := true;
}
yield procedure {:layer 0} SetStoppingFlag(i: Lval int);
refines AtomicSetStoppingFlag;

>-< action {:layer 1} AtomicDeleteReference()
modifies pendingIo, stoppingEvent;
{
    pendingIo := pendingIo - 1;
    if (pendingIo == 0) {
        stoppingEvent := true;
    }
}
yield procedure {:layer 0} DeleteReference();
refines AtomicDeleteReference;

>-< action {:layer 1} AtomicWaitOnStoppingEvent()
{
    assume stoppingEvent;
}
yield procedure {:layer 0} WaitOnStoppingEvent();
refines AtomicWaitOnStoppingEvent;

<- action {:layer 1} AtomicSetStopped()
modifies stopped;
{
    stopped := true;
}
yield procedure {:layer 0} SetStopped();
refines AtomicSetStopped;
