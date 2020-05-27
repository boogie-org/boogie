type {:datatype} Perm;
function {:constructor} Left(i: int): Perm;
function {:constructor} Right(i: int): Perm;

function {:builtin "MapConst"} PermSetConst(bool): [Perm]bool;
function {:builtin "MapOr"} PermSetUnion([Perm]bool, [Perm]bool) : [Perm]bool;

function {:inline} {:linear "perm"} IntCollector(i: int) : [Perm]bool
{
  PermSetConst(false)[Left(i) := true][Right(i) := true]
}
function {:inline} {:linear "perm"} IntSetCollector(iset: [int]bool) : [Perm]bool
{
  (lambda p: Perm :: is#Left(p) && iset[i#Left(p)])
}
function {:inline} {:linear "perm"} PermCollector(p: Perm) : [Perm]bool
{
  PermSetConst(false)[p := true]
}

function {:builtin "MapConst"} IntSetConst(bool): [int]bool;
function {:builtin "MapOr"} IntSetUnion([int]bool, [int]bool): [int]bool;
function {:builtin "MapImp"} IntSetImp([int]bool, [int]bool): [int]bool;
function {:builtin "MapIff"} IntSetIff([int]bool, [int]bool): [int]bool;
function {:inline} IntSetSubset(X: [int]bool, Y: [int]bool): bool
{
    IntSetImp(X, Y) == IntSetConst(true)
}
function {:inline} IntSetEq(X: [int]bool, Y: [int]bool): bool
{
    IntSetIff(X, Y) == IntSetConst(true)
}

function size(set: [int]bool): int;

procedure {:lemma} LemmaAddToSet(set: [int]bool, i: int);
requires !set[i];
ensures size(set[i := true]) ==  size(set) + 1;

procedure {:lemma} LemmaRemoveFromSet(set: [int]bool, i: int);
requires set[i];
ensures size(set[i := false]) ==  size(set) - 1;

procedure {:lemma} LemmaSubsetSizeRelation(a: [int]bool, b: [int]bool);
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

procedure {:atomic} {:layer 1} AtomicIsBarrierOn() returns (b: bool)
{
    b := barrierOn;
}
procedure {:yields} {:layer 0} {:refines "AtomicIsBarrierOn"} IsBarrierOn() returns (b: bool);

procedure {:atomic} {:layer 1} AtomicEnterBarrier({:linear_in "perm"} i: int) returns ({:linear "perm"} p: Perm)
modifies barrierCounter, mutatorsInBarrier;
{
    assert IsMutator(i);
    mutatorsInBarrier[i] := true;
    barrierCounter := barrierCounter - 1;
    p := Right(i);
}
procedure {:yields} {:layer 0} {:refines "AtomicEnterBarrier"} EnterBarrier({:linear_in "perm"} i: int) returns ({:linear "perm"} p: Perm);

procedure {:atomic} {:layer 1} AtomicWaitForBarrierRelease({:linear_in "perm"} p: Perm, {:linear_out "perm"} i: int)
modifies barrierCounter, mutatorsInBarrier;
{
    assert p == Right(i) && mutatorsInBarrier[i];
    assume !barrierOn;
    mutatorsInBarrier[i] := false;
    barrierCounter := barrierCounter + 1;
}
procedure {:yields} {:layer 0} {:refines "AtomicWaitForBarrierRelease"} WaitForBarrierRelease({:linear_in "perm"} p: Perm, {:linear_out "perm"} i: int);

procedure {:atomic} {:layer 1} AtomicSetBarrier(b: bool)
modifies barrierOn;
{
    barrierOn := b;
}
procedure {:yields} {:layer 0} {:refines "AtomicSetBarrier"} SetBarrier(b: bool);

procedure {:atomic} {:layer 1} AtomicWaitBarrier()
{
    assume barrierCounter == 0;
}
procedure {:yields} {:layer 0} {:refines "AtomicWaitBarrier"} WaitBarrier();

procedure {:yields} {:layer 1} Mutator({:linear "perm"} i: int)
requires {:layer 1} IsMutator(i);
requires {:layer 1} BarrierInv(mutatorsInBarrier, barrierCounter);
ensures {:layer 1} BarrierInv(mutatorsInBarrier, barrierCounter);
{
    var b: bool;
    var {:linear "perm"} p: Perm;

    call YieldBarrierInv();
    call b := IsBarrierOn();
    if (b) {
        call YieldBarrierInv();
        call {:layer 1} LemmaAddToSet(mutatorsInBarrier, i);
        call p := EnterBarrier(i);
        par YieldBarrierInv() | YieldMutatorInv(p, i);
        call {:layer 1} LemmaRemoveFromSet(mutatorsInBarrier, i);
        call WaitForBarrierRelease(p, i);
    }
    // access memory here
    call YieldBarrierInv();
}

procedure {:yields} {:layer 1} Collector({:linear "perm"} i: int)
requires {:layer 1} i == 0;
requires {:layer 1} BarrierInv(mutatorsInBarrier, barrierCounter);
ensures {:layer 1} BarrierInv(mutatorsInBarrier, barrierCounter);
{
    call YieldBarrierInv();
    call SetBarrier(true);
    par YieldBarrierInv() | YieldCollectorInv(i, false);
    call WaitBarrier();
    call {:layer 1} LemmaSubsetSizeRelation(mutatorsInBarrier, Mutators);
    par YieldBarrierInv() | YieldCollectorInv(i, true);
    // do root scan here
    assert {:layer 1} mutatorsInBarrier == Mutators;
    call SetBarrier(false);
    call YieldBarrierInv();
}

function BarrierInv(mutatorsInBarrier: [int]bool, barrierCounter: int): bool
{
    IntSetSubset(mutatorsInBarrier, Mutators) &&
    size(mutatorsInBarrier) + barrierCounter == N
}
procedure {:yield_invariant} {:layer 1} YieldBarrierInv();
requires BarrierInv(mutatorsInBarrier, barrierCounter);

function MutatorInv(p: Perm, i: int, mutatorsInBarrier: [int]bool): bool
{
    p == Right(i) && mutatorsInBarrier[i]
}
procedure {:yield_invariant} {:layer 1} YieldMutatorInv({:linear "perm"} p: Perm, i: int);
requires MutatorInv(p, i, mutatorsInBarrier);

function CollectorInv(i: int, done: bool, barrierOn: bool, mutatorsInBarrier: [int]bool): bool
{
    i == 0 && barrierOn &&
    (done ==> mutatorsInBarrier == Mutators)
}
procedure {:yield_invariant} {:layer 1} YieldCollectorInv({:linear "perm"} i: int, done: bool);
requires CollectorInv(i, done, barrierOn, mutatorsInBarrier);

