
// RUN: %boogie /monomorphize /useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:builtin "MapConst"} MapConst<T,U>(U): [T]U;
function {:builtin "MapEq"} MapEq<T,U>([T]U, [T]U) : [T]bool;
function {:builtin "MapIte"} MapIte<T,U>([T]bool, [T]U, [T]U) : [T]U;

function {:builtin "MapOr"} MapOr<T>([T]bool, [T]bool) : [T]bool;
function {:builtin "MapAnd"} MapAnd<T>([T]bool, [T]bool) : [T]bool;
function {:builtin "MapNot"} MapNot<T>([T]bool) : [T]bool;
function {:builtin "MapImp"} MapImp<T>([T]bool, [T]bool) : [T]bool;
function {:builtin "MapIff"} MapIff<T>([T]bool, [T]bool) : [T]bool;

function {:builtin "MapAdd"} MapAdd<T>([T]int, [T]int) : [T]int;
function {:builtin "MapSub"} MapSub<T>([T]int, [T]int) : [T]int;
function {:builtin "MapMul"} MapMul<T>([T]int, [T]int) : [T]int;
function {:builtin "MapDiv"} MapDiv<T>([T]int, [T]int) : [T]int;
function {:builtin "MapMod"} MapMod<T>([T]int, [T]int) : [T]int;
function {:builtin "MapGt"} MapGt<T>([T]int, [T]int) : [T]bool;
function {:builtin "MapGe"} MapGe<T>([T]int, [T]int) : [T]bool;
function {:builtin "MapLt"} MapLt<T>([T]int, [T]int) : [T]bool;
function {:builtin "MapLe"} MapLe<T>([T]int, [T]int) : [T]bool;

procedure add(set: [int]bool, elem: int) returns (set': [int]bool)
ensures set' == MapOr(set, MapConst(false)[elem := true]);
{
    set' := set[elem := true];
}


type {:datatype} Wrapper _;
function {:constructor} Set<E>(set: [E]bool): Wrapper E;
function {:constructor} Multiset<E>(multiset: [E]int): Wrapper E;

type X;
procedure wrapper_add(w: Wrapper X, elem: X) returns (w': Wrapper X)
requires is#Set(w);
ensures is#Set(w');
ensures set#Set(w') == MapOr(set#Set(w), MapConst(false)[elem := true]);
{
    var xset: [X]bool;
    xset := set#Set(w);
    xset := xset[elem := true];
    w' := Set(xset);
}

procedure wrapper_incr(w: Wrapper X, elem: X) returns (w': Wrapper X)
requires is#Multiset(w) && multiset#Multiset(w) == MapConst(42);
ensures is#Multiset(w');
ensures multiset#Multiset(w') == MapIte(MapConst(false)[elem := true], MapConst(0), MapConst(42));
{
    var xmultiset: [X]int;
    xmultiset := multiset#Multiset(w);
    xmultiset[elem] := 0;
    w' := Multiset(xmultiset);
}
