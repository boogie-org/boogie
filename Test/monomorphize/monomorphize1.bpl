// RUN: %parallel-boogie -lib:base -monomorphize -useArrayTheory "%s" > "%t"
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
requires w is Set;
ensures w' is Set;
ensures w'->set == MapOr(w->set, MapConst(false)[elem := true]);
{
    var xset: [X]bool;
    xset := w->set;
    xset := xset[elem := true];
    w' := Set(xset);
}

procedure wrapper_incr(w: Wrapper X, elem: X) returns (w': Wrapper X)
requires w is Multiset && w->multiset == MapConst(42);
ensures w' is Multiset;
ensures w'->multiset == MapIte(MapConst(false)[elem := true], MapConst(0), MapConst(42));
{
    var xmultiset: [X]int;
    xmultiset := w->multiset;
    xmultiset[elem] := 0;
    w' := Multiset(xmultiset);
}
