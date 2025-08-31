// RUN: %parallel-boogie -lib:set_size "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Perm { Left(i: int), Right(i: int) }

datatype Tid { Tid(i: int, {:linear} ps: Set Perm) }

function {:inline} All(i: int): Tid {
    Tid(i, Set_Add(Set_Singleton(Left(i)), Right(i)))
}

const N: int;
axiom 0 < N;
function {:inline} IsMutator(i: int) : bool
{
    1 <= i && i <= N
}
const Mutators: Set Perm;
axiom Mutators->val == (lambda p: Perm:: p is Left && IsMutator(p->i));
axiom Set_Size(Mutators) == N;

var {:layer 0,1} barrierOn: bool;
var {:layer 0,1} barrierCounter: int;
var {:layer 0,1} {:linear} mutatorsInBarrier: Set Perm;

atomic action {:layer 1} AtomicIsBarrierOn() returns (b: bool)
{
    b := barrierOn;
}
yield procedure {:layer 0} IsBarrierOn() returns (b: bool);
refines AtomicIsBarrierOn;

atomic action {:layer 1} AtomicEnterBarrier({:linear_in} tid: Tid) returns ({:linear} tid': Tid)
modifies barrierCounter, mutatorsInBarrier;
{
    var {:linear} p: One Perm;
    var i: int;

    i := tid->i;
    assert IsMutator(i);
    tid' := tid;
    call p := One_Get(tid'->ps, Left(i));
    call One_Put(mutatorsInBarrier, p);
    barrierCounter := barrierCounter - 1;
}
yield procedure {:layer 0} EnterBarrier({:linear_in} tid: Tid) returns ({:linear} tid': Tid);
refines AtomicEnterBarrier;

atomic action {:layer 1} AtomicWaitForBarrierRelease({:linear_in} tid: Tid) returns ({:linear} tid': Tid)
modifies barrierCounter, mutatorsInBarrier;
{
    var {:linear} p: One Perm;
    var i: int;

    i := tid->i;
    assert Set_Contains(tid->ps, Right(i));
    assert Set_Contains(mutatorsInBarrier, Left(i));
    assume !barrierOn;
    call p := One_Get(mutatorsInBarrier, Left(i));
    tid' := tid;
    call One_Put(tid'->ps, p);
    barrierCounter := barrierCounter + 1;
}
yield procedure {:layer 0} WaitForBarrierRelease({:linear_in} tid: Tid) returns ({:linear} tid': Tid);
refines AtomicWaitForBarrierRelease;

atomic action {:layer 1} AtomicSetBarrier(b: bool)
modifies barrierOn;
{
    barrierOn := b;
}
yield procedure {:layer 0} SetBarrier(b: bool);
refines AtomicSetBarrier;

atomic action {:layer 1} AtomicWaitBarrier()
{
    assume barrierCounter == 0;
}
yield procedure {:layer 0} WaitBarrier();
refines AtomicWaitBarrier;

yield procedure {:layer 1} Mutator({:linear} tid: Tid)
requires {:layer 1} IsMutator(tid->i) && tid == All(tid->i);
preserves call BarrierInv();
{
    var b: bool;
    var i: int;
    var {:linear} tid': Tid;

    call b := IsBarrierOn();
    if (b) {
        i := tid->i;
        call BarrierInv();
        call tid' := EnterBarrier(tid);
        call BarrierInv() | MutatorInv(tid');
        call tid' := WaitForBarrierRelease(tid');
        call Move(tid', tid);
    }
    // access memory here
}

yield procedure {:layer 1} Collector({:linear} tid: Tid)
requires {:layer 1} tid == All(0);
preserves call BarrierInv();
{
    call SetBarrier(true);
    call BarrierInv() | CollectorInv(tid, false);
    call WaitBarrier();
    call {:layer 1} Lemma_SubsetSize(mutatorsInBarrier, Mutators);
    call BarrierInv() | CollectorInv(tid, true);
    // do root scan here
    assert {:layer 1} mutatorsInBarrier == Mutators;
    call SetBarrier(false);
}

yield invariant {:layer 1} BarrierInv();
preserves Set_IsSubset(mutatorsInBarrier, Mutators);
preserves Set_Size(mutatorsInBarrier) + barrierCounter == N;

yield invariant {:layer 1} MutatorInv({:linear} tid: Tid);
preserves Set_Contains(tid->ps, Right(tid->i));
preserves Set_Contains(mutatorsInBarrier, Left(tid->i));

yield invariant {:layer 1} CollectorInv({:linear} tid: Tid, done: bool);
preserves tid == All(0) && barrierOn;
preserves done ==> mutatorsInBarrier == Mutators;
