const memLo: int;
const memHi: int;
axiom 0 < memLo && memLo <= memHi;
function memAddr(i:int) returns (bool) { memLo <= i && i < memHi }

const numMutators: int;
axiom 0 < numMutators;
function {:inline} mutatorAddr(i: int) returns (bool) { 1 <= i && i <= numMutators }

const GcTid: int;
axiom GcTid > numMutators;

function {:builtin "MapConst"} MapConstBool(bool): [X]bool;
function {:inline} {:linear "tid"} TidCollector(x: X) : [X]bool
{
  MapConstBool(false)[x := true]
}
function {:inline} {:linear "tid"} TidSetCollector(x: [X]bool) : [X]bool
{
  x
}

function {:builtin "MapOr"} MapOr([X]bool, [X]bool) : [X]bool;
function {:builtin "MapNot"} MapNot(x: [int]bool) : [int]bool;
function {:inline} Subset(X: [int]bool, Y: [int]bool) : (bool)
{
    MapOr(MapNot(X), Y) == MapConstBool(true)
}

type X = int;

var {:layer 0,1} Free: [int]bool;
var {:layer 0,1} freeSpace: int;
var {:layer 0,1} AllocatingAtOrAfter: [int][X]bool;
var {:layer 0,1} NumFreeAtOrAfter: [int]int;

function Size([int]bool) returns (int);
axiom (forall X: [int]bool :: 0 <= Size(X));
axiom (forall X: [int]bool, x: int :: X[x] ==> 1 <= Size(X));
axiom (forall X: [int]bool, x: int :: X[x] ==> X[x:=true] == X);
axiom (forall X: [int]bool, x: int :: !X[x] ==> X[x:=false] == X);
axiom (forall X: [int]bool, x: int :: Size(X[x := false]) + 1 == Size(X[x := true]));
axiom (forall X, Y: [int]bool :: Subset(X, Y) ==> Size(X) < Size(Y) || X == Y);

function {:inline} Invariant(NumFreeAtOrAfter: [int]int, AllocatingAtOrAfter: [int][X]bool, Free: [int]bool, freeSpace: int) : (bool)
{
    Size(AllocatingAtOrAfter[memLo]) + freeSpace == NumFreeAtOrAfter[memLo] &&
    (forall u: int :: Size(AllocatingAtOrAfter[u]) <= NumFreeAtOrAfter[u]) &&
    0 <= freeSpace &&
    (forall u: int, v: int :: memAddr(u) && memAddr(v) && u <= v ==> Subset(AllocatingAtOrAfter[v], AllocatingAtOrAfter[u])) &&
    (forall u: int :: memAddr(u) || NumFreeAtOrAfter[u] == 0) &&
    (forall u: int :: {memAddr(u)} memAddr(u) ==> NumFreeAtOrAfter[u] == (NumFreeAtOrAfter[u+1] + (if Free[u] then 1 else 0)))
}

procedure {:yields} {:layer 0,1} DecrementFreeSpace({:cnst "tid"} tid: X);
ensures {:atomic} |{ A:   assert AllocatingAtOrAfter[memLo] == AllocatingAtOrAfter[memLo][tid := false];
                          assume 0 < freeSpace;
                          freeSpace := freeSpace - 1;
                          AllocatingAtOrAfter[memLo][tid] := true;
                          return true; }|;

procedure {:yields} {:layer 0,1} AllocIfPtrFree({:cnst "tid"} tid:int, ptr:int) returns (spaceFound:bool);
ensures {:atomic} |{
    A: assert memAddr(ptr);
       assert Free[ptr] || memAddr(ptr + 1);
       assert (forall u: int :: AllocatingAtOrAfter[u][tid] <==> memLo <= u && u <= ptr);
       spaceFound := Free[ptr];
       goto B, C;
    B: assume (spaceFound);
       Free[ptr] := false;
       NumFreeAtOrAfter := (lambda u: int :: NumFreeAtOrAfter[u] - (if memLo <= u && u <= ptr then 1 else 0));
       AllocatingAtOrAfter := (lambda u: int :: AllocatingAtOrAfter[u][tid := false]);
       return true;
    C: assume (!spaceFound);
       AllocatingAtOrAfter[ptr+1][tid] := true;
       return true; }|;

procedure {:yields} {:layer 0,1} Reclaim({:cnst "tid"} tid:int);
ensures {:atomic} |{ var ptr: int;
    A: assume memAddr(ptr) && !Free[ptr];
       freeSpace := freeSpace + 1;
       Free[ptr] := true;
       NumFreeAtOrAfter := (lambda u: int :: NumFreeAtOrAfter[u] + (if memLo <= u && u <= ptr then 1 else 0));
       return true; }|;

procedure {:yields} {:layer 1} YieldAlloc({:cnst "tid"} tid:int, i: int)
requires {:layer 1} mutatorAddr(tid);
requires {:expand} {:layer 1} Invariant(NumFreeAtOrAfter, AllocatingAtOrAfter, Free, freeSpace);
requires {:layer 1} (forall u: int :: AllocatingAtOrAfter[u][tid] <==> memLo <= u && u <= i);
ensures {:layer 1} Invariant(NumFreeAtOrAfter, AllocatingAtOrAfter, Free, freeSpace);
ensures {:layer 1} (forall u: int :: AllocatingAtOrAfter[u][tid] <==> memLo <= u && u <= i);
{
    yield;
    assert {:layer 1} mutatorAddr(tid);
    assert {:layer 1} Invariant(NumFreeAtOrAfter, AllocatingAtOrAfter, Free, freeSpace);
    assert {:layer 1} (forall u: int :: {AllocatingAtOrAfter[u][tid]} AllocatingAtOrAfter[u][tid] <==> memLo <= u && u <= i);
}

procedure {:yields} {:layer 1} Malloc({:cnst "tid"} tid: X)
requires {:layer 1} mutatorAddr(tid);
requires {:layer 1} Invariant(NumFreeAtOrAfter, AllocatingAtOrAfter, Free, freeSpace);
requires {:layer 1} (forall u: int :: !AllocatingAtOrAfter[u][tid]);
ensures {:layer 1} Invariant(NumFreeAtOrAfter, AllocatingAtOrAfter, Free, freeSpace);
ensures {:layer 1} (forall u: int :: !AllocatingAtOrAfter[u][tid]);
{
    var i: int;
    var spaceFound: bool;

    call YieldAlloc(tid, 0);

    assert {:layer 1} memAddr(memLo) ==> (forall v: int :: memAddr(v) && memLo <= v ==> Subset(AllocatingAtOrAfter[v], AllocatingAtOrAfter[memLo]));
    assert {:layer 1} memAddr(memLo) ==> (forall v: int :: memAddr(v) && v <= memLo ==> Subset(AllocatingAtOrAfter[memLo], AllocatingAtOrAfter[v]));

    call DecrementFreeSpace(tid);
    i := memLo;

    call YieldAlloc(tid, i);

    while (i < memHi)
    invariant {:layer 1} memAddr(i);
    invariant {:layer 1} Invariant(NumFreeAtOrAfter, AllocatingAtOrAfter, Free, freeSpace);
    invariant {:layer 1} (forall u: int :: AllocatingAtOrAfter[u][tid] <==> memLo <= u && u <= i);
    {
        assert {:layer 1} memAddr(i+1) ==> (forall v: int :: memAddr(v) && i+1 <= v ==> Subset(AllocatingAtOrAfter[v], AllocatingAtOrAfter[i+1]));
        assert {:layer 1} memAddr(i+1) ==> (forall v: int :: memAddr(v) && v <= i+1 ==> Subset(AllocatingAtOrAfter[i+1], AllocatingAtOrAfter[v]));

        call spaceFound := AllocIfPtrFree(tid, i);

        if (spaceFound)
        {
            call YieldAlloc(tid, 0);
            return;
        }
        else
        {
            i := i + 1;
        }
        call YieldAlloc(tid, i);
    }

    yield;
    assert {:layer 1} false;
}

procedure {:yields} {:layer 1} YieldCollect({:cnst "tid"} tid: X)
requires {:layer 1} tid == GcTid;
requires {:layer 1} Invariant(NumFreeAtOrAfter, AllocatingAtOrAfter, Free, freeSpace);
ensures {:layer 1} Invariant(NumFreeAtOrAfter, AllocatingAtOrAfter, Free, freeSpace);
{
    yield;
    assert {:layer 1} tid == GcTid;
    assert {:layer 1} Invariant(NumFreeAtOrAfter, AllocatingAtOrAfter, Free, freeSpace);
}

procedure {:yields} {:layer 1} Collect({:cnst "tid"} tid: X)
requires {:layer 1} tid == GcTid;
requires {:layer 1} Invariant(NumFreeAtOrAfter, AllocatingAtOrAfter, Free, freeSpace);
ensures {:layer 1} Invariant(NumFreeAtOrAfter, AllocatingAtOrAfter, Free, freeSpace);
{
    call YieldCollect(tid);

    while (*)
    invariant {:layer 1} Invariant(NumFreeAtOrAfter, AllocatingAtOrAfter, Free, freeSpace);
    {
        call Reclaim(tid);
        call YieldCollect(tid);
    }
    call YieldCollect(tid);
}
