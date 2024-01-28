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

datatype {:linear "perm"} Perm { Left(i: int), Right(i: int) }

function {:inline}{:linear "perm"} PermCollector(x: Set Perm): [Perm]bool { x->val }

function Size<T>(set: [T]bool): int;
axiom (forall<T> set: [T]bool :: Size(set) >= 0);

pure procedure SizeLemma<T>(X: [T]bool, x: T);
ensures Size(X[x := false]) + 1 == Size(X[x := true]);

pure procedure SubsetSizeRelationLemma<T>(X: [T]bool, Y: [T]bool);
requires MapImp(X, Y) == MapConst(true);
ensures X == Y || Size(X) < Size(Y);

var {:layer 0,3} stoppingFlag: bool;
var {:layer 0,2} stopped: bool;
var {:layer 1,2} {:linear "perm"} usersInDriver: Set Perm;
var {:layer 0,1} pendingIo: int;
var {:layer 0,1} stoppingEvent: bool;

yield invariant {:layer 2} Inv2();
invariant stopped ==> stoppingFlag;

yield invariant {:layer 1} Inv1();
invariant stoppingEvent ==> stoppingFlag && usersInDriver->val == MapConst(false);
invariant pendingIo == Size(usersInDriver->val) + (if stoppingFlag then 0 else 1);

// user code

yield procedure {:layer 2}
User(i: int, {:layer 1,2} {:linear "perm"} l: Set Perm, {:linear "perm"} {:layer 1,2} r: Set Perm)
preserves call Inv2();
preserves call Inv1();
requires {:layer 1, 2} l->val == MapOne(Left(i)) && r->val == MapOne(Right(i));
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

atomic action {:layer 2} AtomicEnter#1(i: int, {:linear_in "perm"} l: Set Perm, {:linear "perm"} r: Set Perm)
modifies usersInDriver;
{
    assume !stoppingFlag;
    usersInDriver := Set_Union(usersInDriver, l);
}
yield procedure {:layer 1}
Enter#1(i: int, {:layer 1} {:linear_in "perm"} l: Set Perm, {:layer 1} {:linear "perm"} r: Set Perm)
refines AtomicEnter#1;
preserves call Inv1();
requires {:layer 1} l->val == MapOne(Left(i)) && r->val == MapOne(Right(i));
{
    call Enter();
    call {:layer 1} SizeLemma(usersInDriver->val, Left(i));
    call {:layer 1} usersInDriver := A(usersInDriver, l);
}

pure action A({:linear_in "perm"} usersInDriver: Set Perm, {:linear_in "perm"} l: Set Perm)
  returns ({:linear "perm"} usersInDriver': Set Perm)
{
    usersInDriver' := Set_Union(usersInDriver, l);
}

left action {:layer 2} AtomicCheckAssert#1(i: int, {:linear "perm"} r: Set Perm)
{
    assert r->val == MapOne(Right(i)) && usersInDriver->val[Left(i)];
    assert !stopped;
}
yield procedure {:layer 1}
CheckAssert#1(i: int, {:layer 1} {:linear "perm"} r: Set Perm)
refines AtomicCheckAssert#1;
preserves call Inv1();
{
    call CheckAssert();
}

left action {:layer 2} AtomicExit(i: int, {:linear_out "perm"} l: Set Perm, {:linear "perm"} r: Set Perm)
modifies usersInDriver;
{
    assert l->val == MapOne(Left(i)) && r->val == MapOne(Right(i));
    call usersInDriver := B(usersInDriver, l);
}
yield procedure {:layer 1}
Exit(i: int, {:layer 1} {:linear_out "perm"} l: Set Perm, {:layer 1} {:linear "perm"} r: Set Perm)
refines AtomicExit;
preserves call Inv1();
{
    call DeleteReference();
    call {:layer 1} SizeLemma(usersInDriver->val, Left(i));
    call {:layer 1} usersInDriver := B(usersInDriver, l);
    call {:layer 1} SubsetSizeRelationLemma(MapConst(false), usersInDriver->val);
}

pure action B({:linear_in "perm"} usersInDriver: Set Perm, {:linear_out "perm"} l: Set Perm)
  returns ({:linear "perm"} usersInDriver': Set Perm)
{
    assert Set_IsSubset(l, usersInDriver);
    usersInDriver' := Set_Difference(usersInDriver, l);
}

// stopper code
type {:linear "stopper"} X = int;

yield procedure {:layer 2} Stopper({:linear "stopper"} i: int)
refines AtomicSetStoppingFlag;
preserves call Inv2();
preserves call Inv1();
{
    call Close(i);
    call WaitAndStop();
}

yield procedure {:layer 1} Close({:linear "stopper"} i: int)
refines AtomicSetStoppingFlag;
preserves call Inv1();
{
    call SetStoppingFlag(i);
    call DeleteReference();
    call {:layer 1} SubsetSizeRelationLemma(MapConst(false), usersInDriver->val);
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

right action {:layer 1,3} AtomicSetStoppingFlag({:linear "stopper"} i: int)
modifies stoppingFlag;
{
    // The first assertion ensures that there is at most one stopper.
    // Otherwise AtomicSetStoppingFlag does not commute with itself.
    assert i == 0;
    assert !stoppingFlag;
    stoppingFlag := true;
}
yield procedure {:layer 0} SetStoppingFlag({:linear "stopper"} i: int);
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
