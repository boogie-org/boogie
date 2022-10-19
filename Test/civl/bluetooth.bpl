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

type {:linear "perm"} {:datatype} Perm;
function {:constructor} Left(i: int): Perm;
function {:constructor} Right(i: int): Perm;

function {:inline} {:linear "perm"} IntCollector(i: int) : [Perm]bool
{
  MapConst(false)[Left(i) := true][Right(i) := true]
}
function {:inline} {:linear "perm"} IntSetCollector(iset: [int]bool) : [Perm]bool
{
  (lambda p: Perm :: p is Left && iset[p->i])
}

function Size<T>(set: [T]bool): int;
axiom (forall set: [int]bool :: Size(set) >= 0);

procedure {:lemma} SizeLemma<T>(X: [T]bool, x: T);
ensures Size(X[x := false]) + 1 == Size(X[x := true]);

procedure {:lemma} SubsetSizeRelationLemma<T>(X: [T]bool, Y: [T]bool);
requires MapImp(X, Y) == MapConst(true);
ensures X == Y || Size(X) < Size(Y);

var {:layer 0,3} stoppingFlag: bool;
var {:layer 0,2} stopped: bool;
var {:layer 1,2} {:linear "perm"} usersInDriver: [int]bool;
var {:layer 0,1} pendingIo: int;
var {:layer 0,1} stoppingEvent: bool;

procedure {:yield_invariant} {:layer 2} Inv2();
requires stopped ==> stoppingFlag;

procedure {:yield_invariant} {:layer 1} Inv1();
requires stoppingEvent ==> stoppingFlag && usersInDriver == MapConst(false);
requires pendingIo == Size(usersInDriver) + (if stoppingFlag then 0 else 1);

procedure {:yields} {:layer 2}
{:yield_preserves "Inv2"}
{:yield_preserves "Inv1"}
User({:linear "perm"} i: int)
{
    var {:layer 1,2} {:linear "perm"} p: Perm;

    while (*)
    invariant {:yields} {:layer 2} {:yield_loop "Inv2"} true;
    invariant {:yields} {:layer 1} {:yield_loop "Inv1"} true;
    {
        call p := Enter#1(i);
        call CheckAssert#1(p, i);
        call Exit(p, i);
    }
}

procedure {:yields} {:layer 2} {:refines "AtomicSetStoppingFlag"}
{:yield_preserves "Inv2"}
{:yield_preserves "Inv1"}
Stopper({:linear_in "perm"} i: int)
requires {:layer 2} i == 0;
{
    call Close(i);
    call WaitAndStop();
}

procedure {:atomic} {:layer 2} AtomicEnter#1({:linear_in "perm"} i: int) returns ({:linear "perm"} p: Perm)
modifies usersInDriver;
{
    assume !stoppingFlag;
    usersInDriver[i] := true;
    p := Right(i);
}
procedure {:yields} {:layer 1} {:refines "AtomicEnter#1"}
{:yield_preserves "Inv1"}
Enter#1({:linear_in "perm"} i: int) returns ({:layer 1} {:linear "perm"} p: Perm)
{
    call Enter();
    call {:layer 1} SizeLemma(usersInDriver, i);
    call p := AddToBarrier(i);
}

procedure {:left} {:layer 2} AtomicCheckAssert#1({:layer 1} {:linear "perm"} p: Perm, i: int)
{
    assert p == Right(i) && usersInDriver[i];
    assert !stopped;
}
procedure {:yields} {:layer 1} {:refines "AtomicCheckAssert#1"}
{:yield_preserves "Inv1"}
CheckAssert#1({:layer 1} {:linear "perm"} p: Perm, i: int)
{
    call CheckAssert();
}

procedure {:left} {:layer 2} AtomicExit({:layer 1} {:linear_in "perm"} p: Perm, {:linear_out "perm"} i: int)
modifies usersInDriver;
{
    assert p == Right(i) && usersInDriver[i];
    usersInDriver[i] := false;
}
procedure {:yields} {:layer 1} {:refines "AtomicExit"}
{:yield_preserves "Inv1"}
Exit({:layer 1} {:linear_in "perm"} p: Perm, {:linear_out "perm"} i: int)
{
    call DeleteReference();
    call {:layer 1} SizeLemma(usersInDriver, i);
    call RemoveFromBarrier(p, i);
    call {:layer 1} SubsetSizeRelationLemma(MapConst(false), usersInDriver);
}

procedure {:yields} {:layer 1} {:refines "AtomicSetStoppingFlag"}
{:yield_preserves "Inv1"}
Close({:linear_in "perm"} i: int)
{
    call SetStoppingFlag(i);
    call DeleteReference();
    call {:layer 1} SubsetSizeRelationLemma(MapConst(false), usersInDriver);
}

procedure {:atomic} {:layer 2} AtomicWaitAndStop()
modifies stopped;
{
    assume usersInDriver == MapConst(false);
    stopped := true;
}
procedure {:yields} {:layer 1} {:refines "AtomicWaitAndStop"}
{:yield_preserves "Inv1"}
WaitAndStop()
{
    call WaitOnStoppingEvent();
    call SetStopped();
}

procedure {:intro} {:layer 1} AddToBarrier({:linear_in "perm"} i: int) returns ({:linear "perm"} p: Perm)
modifies usersInDriver;
{
    usersInDriver[i] := true;
    p := Right(i);
}

procedure {:intro} {:layer 1} RemoveFromBarrier({:linear_in "perm"} p: Perm, {:linear_out "perm"} i: int)
modifies usersInDriver;
{
    assert p == Right(i) && usersInDriver[i];
    usersInDriver[i] := false;
}

procedure {:atomic} {:layer 1} AtomicEnter()
modifies pendingIo;
{
    assume !stoppingFlag;
    pendingIo := pendingIo + 1;
}
procedure {:yields} {:layer 0} {:refines "AtomicEnter"} Enter();

procedure {:atomic} {:layer 1} AtomicCheckAssert()
{
    assert !stopped;
}
procedure {:yields} {:layer 0} {:refines "AtomicCheckAssert"} CheckAssert();

procedure {:right} {:layer 1,3} AtomicSetStoppingFlag({:linear_in "perm"} i: int)
modifies stoppingFlag;
{
    assert i == 0 && !stoppingFlag;
    stoppingFlag := true;
}
procedure {:yields} {:layer 0} {:refines "AtomicSetStoppingFlag"} SetStoppingFlag({:linear_in "perm"} i: int);

procedure {:atomic} {:layer 1} AtomicDeleteReference()
modifies pendingIo, stoppingEvent;
{
    pendingIo := pendingIo - 1;
    if (pendingIo == 0) {
        stoppingEvent := true;
    }
}
procedure {:yields} {:layer 0} {:refines "AtomicDeleteReference"} DeleteReference();

procedure {:atomic} {:layer 1} AtomicWaitOnStoppingEvent()
{
    assume stoppingEvent;
}
procedure {:yields} {:layer 0} {:refines "AtomicWaitOnStoppingEvent"} WaitOnStoppingEvent();

procedure {:left} {:layer 1} AtomicSetStopped()
modifies stopped;
{
    stopped := true;
}
procedure {:yields} {:layer 0} {:refines "AtomicSetStopped"} SetStopped();
