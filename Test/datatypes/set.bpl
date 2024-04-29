// RUN: %parallel-boogie /lib:base "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure Test1() {
  var a, b, c, d: Set int;
  a := Set_Empty();
  assert Set_Size(a) == 0;
  a := Set_Singleton(3);
  assert Set_Size(a) == 1;
  b := Set_Add(a, 5);
  assert Set_Size(b) == 2;
  c := Set_Union(b, Set_Singleton(6));
  assert Set_Size(Set_Singleton(6)) == 1;
  assert Set_Size(c) == 3;
  d := Set_Add(c, 3);
  assert Set_Size(d) == 3;
  d := Set_Remove(c, 3);
  assert Set_Size(d) == 2;
}

procedure Test2() {
  var a, b, c: Set int;
  a := Set_Singleton(3);
  b := Set_Add(a, 5);
  c := Set_Union(b, Set_Singleton(6));
  assert Set_Size(Set_Singleton(6)) == 1;
  assert Set_Size(c) == 3;
}

procedure Test3() {
  var a, b, c: Set int;
  a := Set_Singleton(3);
  b := Set_Union(a, Set_Singleton(5));
  assert Set_Size(Set_Singleton(5)) == 1;
  c := Set_Union(b, Set_Singleton(6));
  assert Set_Size(Set_Singleton(6)) == 1;
  assert Set_Size(c) == 3;
}

procedure Test4(a: Set int, b: Set int) {
  assert Set_Size(Set_Union(a, b)) + Set_Size(Set_Intersection(a, b)) == Set_Size(a) + Set_Size(b);
}

procedure Test5(a: Set int, b: Set int)
requires Set_IsSubset(a, b);
{
  assert Set_Size(a) <= Set_Size(b);
  assert Set_Size(a) + Set_Size(Set_Difference(b, a)) == Set_Size(b);
  assert a == b || Set_Size(a) < Set_Size(b);
}

procedure Test6(a: Set int, b: Set int)
requires Set_IsDisjoint(a, b);
{
  assert Set_Size(Set_Union(a, b)) == Set_Size(a) + Set_Size(b);
}

procedure Test7(a: Set int, t: int)
{
  assert Set_Size(Set_Add(a, t)) == Set_Size(Set_Remove(a, t)) + 1;
}

const min: int;
const max: int;
axiom min <= max;

var isFree: [int]bool;

procedure Alloc() returns (i: int)
requires 0 < Set_Size(FreePositions(isFree, min));
ensures old(isFree[i]);
ensures isFree == old(isFree)[i := false];
modifies isFree;
{
  i := min;
  call FreePositionsDefinition(isFree, i);
  while (i < max)
  invariant min <= i && i < max;
  invariant 0 < Set_Size(FreePositions(isFree, i));
  {
    call FreePositionsDefinition(isFree, i);
    if (isFree[i]) {
      isFree[i] := false;
      return;
    }
    i := i + 1;
    call FreePositionsDefinition(isFree, i);
  }
  assert false;
}

function FreePositions(isFree: [int]bool, i: int): Set int;

pure procedure FreePositionsDefinition(isFree: [int]bool, i: int)
ensures FreePositions(isFree, i) ==
        if (i >= max) then Set_Empty() else (var t := FreePositions(isFree, i + 1); if (isFree[i]) then Set_Add(t, i) else t);
{
    var set: Set int;
    call set := FreePositionsCompute(isFree, i);
}

pure procedure FreePositionsCompute(isFree: [int]bool, i: int) returns (set: Set int)
ensures set == Set((lambda x: int :: i <= x && x < max && isFree[x]));
ensures set ==
        if (i >= max) then Set_Empty() else (var t := FreePositions(isFree, i + 1); if (isFree[i]) then Set_Add(t, i) else t);
free ensures set == FreePositions(isFree, i);
{
  if (i >= max) {
    set := Set_Empty();
  } else {
    assert i < i + 1 && i + 1 <= max;
    call set := FreePositionsCompute(isFree, i + 1);
    if (isFree[i]) {
      set := Set_Add(set, i);
    }
  }
}
