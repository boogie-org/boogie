function Set_Size<T>(a: Set T) : int;

axiom (forall<T> a: Set T :: 0 <= Set_Size(a));

axiom (forall<T> :: Set_Size(Set_Empty(): Set T) == 0);

axiom (forall<T> a: Set T, t: T :: {Set_Add(a, t)} Set_Size(Set_Add(a, t)) == if Set_Contains(a, t) then Set_Size(a) else Set_Size(a) + 1);

axiom (forall<T> a: Set T, t: T :: {Set_Remove(a, t)} Set_Size(Set_Remove(a, t)) == if Set_Contains(a, t) then Set_Size(a) - 1 else Set_Size(a));

axiom (forall<T> a: Set T, b: Set T :: {Set_Size(Set_Difference(a, b))} {Set_Size(Set_Intersection(a, b))}
        Set_Size(a) == Set_Size(Set_Difference(a, b)) + Set_Size(Set_Intersection(a, b)));

axiom (forall<T> a: Set T, b: Set T :: {Set_Size(Set_Union(a, b))} {Set_Size(Set_Intersection(a, b))}
        Set_Size(Set_Union(a, b)) + Set_Size(Set_Intersection(a, b)) == Set_Size(a) + Set_Size(b));

pure procedure Lemma_SetSize_Add<T>(a: Set T, t: T) returns (b: Set T);
requires !Set_Contains(a, t);
ensures b == Set_Add(a, t);
ensures Set_Size(b) == Set_Size(a) + 1;

pure procedure Lemma_SetSize_Remove<T>(a: Set T, t: T) returns (b: Set T);
requires Set_Contains(a, t);
ensures b == Set_Remove(a, t);
ensures Set_Size(b) + 1 == Set_Size(a);

pure procedure Lemma_SetSize_Subset<T>(a: Set T, b: Set T);
requires Set_IsSubset(a, b);
ensures a == b || Set_Size(a) < Set_Size(b);
