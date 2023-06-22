// RUN: %parallel-boogie -lib:base "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure add(set: [int]bool, elem: int) returns (set': [int]bool)
ensures set' == MapOr(set, MapConst(false)[elem := true]);
{
    set' := set[elem := true];
}

datatype Wrapper<E> {
  WrapperSet(set: [E]bool),
  WrapperMultiset(multiset: [E]int)
}

type X;
procedure wrapper_add(w: Wrapper X, elem: X) returns (w': Wrapper X)
requires w is WrapperSet;
ensures w' is WrapperSet;
ensures w'->set == MapOr(w->set, MapConst(false)[elem := true]);
{
    var xset: [X]bool;
    xset := w->set;
    xset := xset[elem := true];
    w' := WrapperSet(xset);
}

procedure wrapper_incr(w: Wrapper X, elem: X) returns (w': Wrapper X)
requires w is WrapperMultiset && w->multiset == MapConst(42);
ensures w' is WrapperMultiset;
ensures w'->multiset == MapIte(MapConst(false)[elem := true], MapConst(0), MapConst(42));
{
    var xmultiset: [X]int;
    xmultiset := w->multiset;
    xmultiset[elem] := 0;
    w' := WrapperMultiset(xmultiset);
}
