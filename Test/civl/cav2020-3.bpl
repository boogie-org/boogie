// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

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

function {:inline} IntSetSubset(X: [int]bool, Y: [int]bool): bool
{
    MapImp(X, Y) == MapConst(true)
}
function {:inline} IntSetEq(X: [int]bool, Y: [int]bool): bool
{
    MapIff(X, Y) == MapConst(true)
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

procedure {:yields} {:layer 1}
{:yield_preserves "BarrierInv"}
Mutator({:linear "perm"} i: int)
requires {:layer 1} IsMutator(i);
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

procedure {:yields} {:layer 1}
{:yield_preserves "BarrierInv"}
Collector({:linear "perm"} i: int)
requires {:layer 1} i == 0;
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

procedure {:yield_invariant} {:layer 1} BarrierInv();
requires IntSetSubset(mutatorsInBarrier, Mutators);
requires size(mutatorsInBarrier) + barrierCounter == N;

procedure {:yield_invariant} {:layer 1} MutatorInv({:linear "perm"} p: Perm, i: int);
requires p == Right(i) && mutatorsInBarrier[i];

procedure {:yield_invariant} {:layer 1} CollectorInv({:linear "perm"} i: int, done: bool);
requires i == 0 && barrierOn;
requires done ==> mutatorsInBarrier == Mutators;
