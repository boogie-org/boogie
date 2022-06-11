// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*
This example is inspired by coordination seen in device drivers.
A stopping thread is attempting to clean up driver resources and
forces user threads to stop accessing the driver resources.
This proof works for arbitrary number of user threads.
This example provides another instance of barrier synchronization;
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
  (lambda p: Perm :: is#Left(p) && iset[i#Left(p)])
}

function Size<T>(set: [T]bool): int;
axiom (forall set: [int]bool :: Size(set) >= 0);

procedure {:lemma} SizeLemma<T>(X: [T]bool, x: T);
ensures Size(X[x := false]) + 1 == Size(X[x := true]);

procedure {:lemma} SubsetSizeRelationLemma<T>(X: [T]bool, Y: [T]bool);
requires MapImp(X, Y) == MapConst(true);
ensures X == Y || Size(X) < Size(Y);

function {:inline} IsUser(i: int) : bool
{
    1 <= i
}

var {:layer 0,3} stoppingFlag: bool;
var {:layer 0,2} stopped: bool;
var {:layer 1,2} {:linear "perm"} usersInBarrier: [int]bool;
var {:layer 0,1} pendingIo: int;
var {:layer 0,1} stoppingEvent: bool;

procedure {:yield_invariant} {:layer 2} Inv2();
requires stopped ==> stoppingFlag;

procedure {:yield_invariant} {:layer 1} Inv1();
requires stoppingEvent ==> stoppingFlag;
requires stoppingEvent ==> usersInBarrier == MapConst(false);
requires stoppingFlag ==> Size(usersInBarrier) == pendingIo;
requires !stoppingFlag ==> 1 + Size(usersInBarrier) == pendingIo;

procedure {:yields} {:layer 2}
{:yield_preserves "Inv2"}
{:yield_preserves "Inv1"}
User({:linear "perm"} i: int)
requires {:layer 2} IsUser(i);
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

procedure {:yields} {:layer 2} {:refines "AtomicSpec"}
{:yield_preserves "Inv2"}
{:yield_preserves "Inv1"}
Stopper({:linear "perm"} i: int)
requires {:layer 2} i == 0;
{
    call SetStoppingFlagAndClose(i);
    call WaitAndStop();
}

procedure {:atomic} {:layer 2} AtomicEnter#1({:linear_in "perm"} i: int) returns ({:linear "perm"} p: Perm)
modifies usersInBarrier;
{
    assert IsUser(i);
    assume !stoppingFlag;
    usersInBarrier[i] := true;
    p := Right(i);
}
procedure {:yields} {:layer 1} {:refines "AtomicEnter#1"}
{:yield_preserves "Inv1"}
Enter#1({:linear_in "perm"} i: int) returns ({:layer 1} {:linear "perm"} p: Perm)
{
    call Enter(i);
    call {:layer 1} SizeLemma(usersInBarrier, i);
    call p := AddToBarrier(i);
}

procedure {:left} {:layer 2} AtomicCheckAssert#1({:layer 1} {:linear "perm"} p: Perm, i: int)
{
    assert p == Right(i) && IsUser(i) && usersInBarrier[i];
    assert !stopped;
}
procedure {:yields} {:layer 1} {:refines "AtomicCheckAssert#1"}
{:yield_preserves "Inv1"}
CheckAssert#1({:layer 1} {:linear "perm"} p: Perm, i: int)
{
    call CheckAssert();
}

procedure {:left} {:layer 2} AtomicExit({:layer 1} {:linear_in "perm"} p: Perm, {:linear_out "perm"} i: int)
modifies usersInBarrier;
{
    assert p == Right(i) && IsUser(i) && usersInBarrier[i];
    usersInBarrier[i] := false;
}
procedure {:yields} {:layer 1} {:refines "AtomicExit"}
{:yield_preserves "Inv1"}
Exit({:layer 1} {:linear_in "perm"} p: Perm, {:linear_out "perm"} i: int)
{
    call Close();
    call {:layer 1} SizeLemma(usersInBarrier, i);
    call RemoveFromBarrier(p, i);
    call {:layer 1} SubsetSizeRelationLemma(MapConst(false), usersInBarrier);
}

procedure {:right} {:layer 1,3} AtomicSpec({:linear "perm"} i: int)
modifies stoppingFlag;
{
    assert i == 0 && !stoppingFlag;
    stoppingFlag := true;
}
procedure {:yields} {:layer 1} {:refines "AtomicSpec"}
{:yield_preserves "Inv1"}
SetStoppingFlagAndClose({:linear "perm"} i: int)
{
    call SetStoppingFlag(i);
    call Close();
    call {:layer 1} SubsetSizeRelationLemma(MapConst(false), usersInBarrier);
}

procedure {:atomic} {:layer 2} AtomicWaitAndStop()
modifies stopped;
{
    assume usersInBarrier == MapConst(false);
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
modifies usersInBarrier;
{
    usersInBarrier[i] := true;
    p := Right(i);
}

procedure {:intro} {:layer 1} RemoveFromBarrier({:linear_in "perm"} p: Perm, {:linear_out "perm"} i: int)
modifies usersInBarrier;
{
    assert p == Right(i) && usersInBarrier[i];
    usersInBarrier[i] := false;
}

procedure {:atomic} {:layer 1} AtomicEnter({:linear "perm"} i: int)
modifies pendingIo;
{
    assert IsUser(i);
    assume !stoppingFlag;
    pendingIo := pendingIo + 1;
}
procedure {:yields} {:layer 0} {:refines "AtomicEnter"} Enter({:linear "perm"} i: int);

procedure {:atomic} {:layer 1} AtomicCheckAssert()
{
    assert !stopped;
}
procedure {:yields} {:layer 0} {:refines "AtomicCheckAssert"} CheckAssert();

procedure {:right} {:layer 1} AtomicSetStoppingFlag({:linear "perm"} i: int)
modifies stoppingFlag;
{
    assert i == 0 && !stoppingFlag;
    stoppingFlag := true;
}
procedure {:yields} {:layer 0} {:refines "AtomicSetStoppingFlag"} SetStoppingFlag({:linear "perm"} i: int);

procedure {:atomic} {:layer 1} AtomicClose()
modifies pendingIo, stoppingEvent;
{
    pendingIo := pendingIo - 1;
    if (pendingIo == 0) {
        stoppingEvent := true;
    }
}
procedure {:yields} {:layer 0} {:refines "AtomicClose"} Close();

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
