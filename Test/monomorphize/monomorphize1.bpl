
// RUN: %parallel-boogie -lib -monomorphize -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

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
