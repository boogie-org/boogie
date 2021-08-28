// RUN: %parallel-boogie -monomorphize "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Vec T;
function Vec#Empty<T>(): Vec T;
function Vec#Unit<T>(t: T): Vec T;
function Vec#Concat<T>(s1: Vec T, s2: Vec T): Vec T;
function Vec#Extract<T>(s: Vec T, pos: int, len: int): Vec T;
function Vec#Update<T>(s: Vec T, pos: int, t: T): Vec T;
function Vec#Len<T>(s: Vec T): int;
function Vec#Select<T>(s: Vec T, pos: int): T;
function Vec#IsEqual<T>(s1: Vec T, s2: Vec T): bool;
axiom {:ctor "Vec"} (forall<U> :: Vec#Len(Vec#Empty() : Vec U) == 0);
axiom {:ctor "Vec"} (forall<U> e: U :: Vec#Len(Vec#Unit(e)) == 1);

type Set T;
function Set#Empty<T>(): Set T;
function Set#Unit<T>(t: T): Set T;
function Set#Add<T>(s: Set T, t: T): Set T;
function Set#Remove<T>(s: Set T, t: T): Set T;
function Set#Union<T>(s1: Set T, s2: Set T): Set T;
function Set#Intersection<T>(s1: Set T, s2: Set T): Set T;
function Set#Difference<T>(s1: Set T, s2: Set T): Set T;
function Set#Size<T>(s: Set T): int;
function Set#Contains<T>(s: Set T, t: T): bool;
function Set#IsEqual<T>(s1: Set T, s2: Set T): bool;
axiom {:ctor "Set"} (forall<U> :: Set#Size(Set#Empty() : Set U) == 0);
axiom {:ctor "Set"} (forall<U> e: U :: Set#Size(Set#Unit(e)) == 1);

procedure empty_vec() returns (v: Vec int)
ensures Vec#Len(v) == 0;
{
    v := Vec#Empty();
}

procedure unit_vec(e: int) returns (v: Vec int)
ensures Vec#Len(v) == 1;
{
    v := Vec#Unit(e);
}

procedure empty_set() returns (v: Set int)
ensures Set#Size(v) == 0;
{
    v := Set#Empty();
}

procedure unit_set(e: int) returns (v: Set int)
ensures Set#Size(v) == 1;
{
    v := Set#Unit(e);
}

type K;

procedure empty_vec_k() returns (v: Vec K)
ensures Vec#Len(v) == 0;
{
    v := Vec#Empty();
}

procedure empty_set_k() returns (v: Set K)
ensures Set#Size(v) == 0;
{
    v := Set#Empty();
}

