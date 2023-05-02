// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype {:linear "perm"} Perm { Left(i: int), Right(i: int) }

function {:inline} {:linear "perm"} IntCollector(i: int) : [Perm]bool
{
  MapConst(false)[Left(i) := true][Right(i) := true]
}
function {:inline} {:linear "perm"} IntSetCollector(iset: [int]bool) : [Perm]bool
{
  (lambda p: Perm :: p is Left && iset[p->i])
}

function {:inline} IntSetSubset(X: [int]bool, Y: [int]bool): bool
{
    MapImp(X, Y) == MapConst(true)
}
function {:inline} IntSetEq(X: [int]bool, Y: [int]bool): bool
{
    MapIff(X, Y) == MapConst(true)
}

function size(set: [int]bool): int;

pure procedure LemmaAddToSet(set: [int]bool, i: int);
requires !set[i];
ensures size(set[i := true]) ==  size(set) + 1;

pure procedure LemmaRemoveFromSet(set: [int]bool, i: int);
requires set[i];
ensures size(set[i := false]) ==  size(set) - 1;

pure procedure LemmaSubsetSizeRelation(a: [int]bool, b: [int]bool);
requires IntSetSubset(a, b);
ensures a == b || size(a) < size(b);

const N: int;
axiom 0 < N;
function {:inline} IsMutator(i: int) : bool
{
    1 <= i && i <= N
}
const Mutators: [int]bool;
axiom Mutators == (lambda x: int:: IsMutator(x));
axiom size(Mutators) == N;

var {:layer 0,1} barrierOn: bool;
var {:layer 0,1} barrierCounter: int;
var {:layer 0,1} {:linear "perm"} mutatorsInBarrier: [int]bool;

>-< action {:layer 1} AtomicIsBarrierOn() returns (b: bool)
{
    b := barrierOn;
}
yield procedure {:layer 0} IsBarrierOn() returns (b: bool);
refines AtomicIsBarrierOn;

>-< action {:layer 1} AtomicEnterBarrier({:linear_in "perm"} i: int) returns ({:linear "perm"} p: Perm)
modifies barrierCounter, mutatorsInBarrier;
{
    assert IsMutator(i);
    mutatorsInBarrier[i] := true;
    barrierCounter := barrierCounter - 1;
    p := Right(i);
}
yield procedure {:layer 0} EnterBarrier({:linear_in "perm"} i: int) returns ({:linear "perm"} p: Perm);
refines AtomicEnterBarrier;

>-< action {:layer 1} AtomicWaitForBarrierRelease({:linear_in "perm"} p: Perm, {:linear_out "perm"} i: int)
modifies barrierCounter, mutatorsInBarrier;
{
    assert p == Right(i) && mutatorsInBarrier[i];
    assume !barrierOn;
    mutatorsInBarrier[i] := false;
    barrierCounter := barrierCounter + 1;
}
yield procedure {:layer 0} WaitForBarrierRelease({:linear_in "perm"} p: Perm, {:linear_out "perm"} i: int);
refines AtomicWaitForBarrierRelease;

>-< action {:layer 1} AtomicSetBarrier(b: bool)
modifies barrierOn;
{
    barrierOn := b;
}
yield procedure {:layer 0} SetBarrier(b: bool);
refines AtomicSetBarrier;

>-< action {:layer 1} AtomicWaitBarrier()
{
    assume barrierCounter == 0;
}
yield procedure {:layer 0} WaitBarrier();
refines AtomicWaitBarrier;

yield procedure {:layer 1} Mutator({:linear "perm"} i: int)
requires {:layer 1} IsMutator(i);
preserves call BarrierInv();
{
    var b: bool;
    var {:linear "perm"} p: Perm;

    call b := IsBarrierOn();
    if (b) {
        call BarrierInv();
        call {:layer 1} LemmaAddToSet(mutatorsInBarrier, i);
        call p := EnterBarrier(i);
        par BarrierInv() | MutatorInv(p, i);
        call {:layer 1} LemmaRemoveFromSet(mutatorsInBarrier, i);
        call WaitForBarrierRelease(p, i);
    }
    // access memory here
}

yield procedure {:layer 1} Collector({:linear "perm"} i: int)
requires {:layer 1} i == 0;
preserves call BarrierInv();
{
    call SetBarrier(true);
    par BarrierInv() | CollectorInv(i, false);
    call WaitBarrier();
    call {:layer 1} LemmaSubsetSizeRelation(mutatorsInBarrier, Mutators);
    par BarrierInv() | CollectorInv(i, true);
    // do root scan here
    assert {:layer 1} mutatorsInBarrier == Mutators;
    call SetBarrier(false);
}

yield invariant {:layer 1} BarrierInv();
invariant IntSetSubset(mutatorsInBarrier, Mutators);
invariant size(mutatorsInBarrier) + barrierCounter == N;

yield invariant {:layer 1} MutatorInv({:linear "perm"} p: Perm, i: int);
invariant p == Right(i) && mutatorsInBarrier[i];

yield invariant {:layer 1} CollectorInv({:linear "perm"} i: int, done: bool);
invariant i == 0 && barrierOn;
invariant done ==> mutatorsInBarrier == Mutators;
