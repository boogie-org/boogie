/// maps
function {:builtin "MapConst"} MapConst<T,U>(U): [T]U;
function {:builtin "MapEq"} MapEq<T,U>([T]U, [T]U) : [T]bool;
function {:builtin "MapIte"} MapIte<T,U>([T]bool, [T]U, [T]U) : [T]U;

function {:builtin "MapOr"} MapOr<T>([T]bool, [T]bool) : [T]bool;
function {:builtin "MapAnd"} MapAnd<T>([T]bool, [T]bool) : [T]bool;
function {:builtin "MapNot"} MapNot<T>([T]bool) : [T]bool;
function {:builtin "MapImp"} MapImp<T>([T]bool, [T]bool) : [T]bool;
function {:builtin "MapIff"} MapIff<T>([T]bool, [T]bool) : [T]bool;
function {:inline} MapDiff<T>(a: [T]bool, b: [T]bool) : [T]bool
{
  MapAnd(a, MapNot(b))
}

function {:builtin "MapAdd"} MapAdd<T>([T]int, [T]int) : [T]int;
function {:builtin "MapSub"} MapSub<T>([T]int, [T]int) : [T]int;
function {:builtin "MapMul"} MapMul<T>([T]int, [T]int) : [T]int;
function {:builtin "MapDiv"} MapDiv<T>([T]int, [T]int) : [T]int;
function {:builtin "MapMod"} MapMod<T>([T]int, [T]int) : [T]int;
function {:builtin "MapGt"} MapGt<T>([T]int, [T]int) : [T]bool;
function {:builtin "MapGe"} MapGe<T>([T]int, [T]int) : [T]bool;
function {:builtin "MapLt"} MapLt<T>([T]int, [T]int) : [T]bool;
function {:builtin "MapLe"} MapLe<T>([T]int, [T]int) : [T]bool;

function {:inline} MapOne<T>(t: T): [T]bool
{
  MapConst(false)[t := true]
}

function {:inline} ToMultiset<T>(set: [T]bool): [T]int
{
  MapIte(set, MapConst(1), MapConst(0))
}

function {:inline} IsSubset<T>(a: [T]bool, b: [T]bool) : bool
{
  MapImp(a, b) == MapConst(true)
}

function {:inline} IsDisjoint<T>(a: [T]bool, b: [T]bool) : bool {
  MapAnd(a, b) == MapConst(false)
}

function {:inline} Id<T>(t: T): T
{
  t
}

function Default<T>(): T;

/// option
datatype Option<T> { None(), Some(t: T) }

/// vectors
datatype Vec<T> { Vec(contents: [int]T, len: int) }

const Identity: [int]int;
axiom (forall x: int :: Identity[x] == x);

function {:inline} AtLeast(x: int): [int]bool
{
  MapLe(MapConst(x), Identity)
}
function {:inline} Range(from: int, n: int): [int]bool {
  MapDiff(AtLeast(from), AtLeast(from + n))
}

axiom {:ctor "Vec"} (forall<T> x: Vec T :: {x->len}{x->contents} MapIte(Range(0, x->len), MapConst(Default()), x->contents) == MapConst(Default()));
axiom {:ctor "Vec"} (forall<T> x: Vec T :: {x->len} x->len >= 0);

function {:inline} Vec_Empty<T>(): Vec T
{
  Vec(MapConst(Default()), 0)
}
function {:inline} Vec_Append<T>(v: Vec T, x: T) : Vec T
{
  Vec(v->contents[v->len := x], v->len + 1)
}
function {:inline} Vec_Update<T>(v: Vec T, i: int, x: T) : Vec T
{
  if (0 <= i && i < v->len) then Vec(v->contents[i := x], v->len) else v
}
function {:inline} Vec_Nth<T>(v: Vec T, i: int): T
{
  v->contents[i]
}
function {:inline} Vec_Len<T>(v: Vec T): int
{
  v->len
}

function {:inline} Vec_Concat<T>(v1: Vec T, v2: Vec T): Vec T {
    Vec(
        (lambda {:pool "Concat"} i: int ::
            if (i < 0) then Default()
            else if (0 <= i && i < Vec_Len(v1)) then Vec_Nth(v1, i)
            else if (Vec_Len(v1) <= i && i < Vec_Len(v1) + Vec_Len(v2)) then Vec_Nth(v2, i - Vec_Len(v1))
            else Default()),
        Vec_Len(v1) + Vec_Len(v2)
       )
}

function {:inline} Vec_Slice<T>(v: Vec T, i: int, j: int): Vec T {
    (
        var cond := 0 <= i && i < j && j <= v->len;
        Vec(
            (lambda {:pool "Slice"} k: int ::
                if (cond && 0 <= k && k < j - i) then Vec_Nth(v, k + i)
                else Default()),
            if (cond) then j - i else 0
           )
    )
}

function {:inline} Vec_Swap<T>(v: Vec T, i: int, j: int): Vec T {
    (
        var cond := 0 <= i && i < v->len && 0 <= j && j < v->len;
        Vec(v->contents[i := v->contents[if (cond) then j else i]][j := v->contents[if (cond) then i else j]], v->len)
    )
}

function {:inline} Vec_Remove<T>(v: Vec T): Vec T {
    (
        var cond, new_len := 0 < v->len, v->len - 1;
        Vec(v->contents[new_len := if (cond) then Default() else v->contents[new_len]], if (cond) then new_len else v->len)
    )
}

// extensionality lemma to be used explicitly by the programmer
procedure Vec_Ext<T>(A: Vec T, B: Vec T) returns (i: int);
ensures A == B || Vec_Len(A) != Vec_Len(B) || Vec_Nth(A, i) != Vec_Nth(B, i);

/// sequences
type {:builtin "Seq"} Seq _;
function {:builtin "seq.empty"} Seq_Empty<T>(): Seq T;
function {:builtin "seq.len"} Seq_Len<T>(a: Seq T): int;
function {:builtin "seq.++"} Seq_Concat<T>(a: Seq T, b: Seq T): Seq T;
function {:builtin "seq.unit"} Seq_Unit<T>(v: T): Seq T;
function {:builtin "seq.nth"} Seq_Nth<T>(a: Seq T, i: int): T;
function {:builtin "seq.extract"} Seq_Extract<T>(a: Seq T, pos: int, length: int): Seq T;

/// finite sets
datatype Set<T> {
  Set(val: [T]bool)
}

function Set_Size<T>(a: Set T) : int;

axiom (forall<T> a: Set T :: a == Set_Empty() || 0 < Set_Size(a));

axiom (forall<T> :: Set_Size(Set_Empty(): Set T) == 0);

axiom (forall<T> a: Set T, t: T :: {Set_Add(a, t)} Set_Size(Set_Add(a, t)) == if Set_Contains(a, t) then Set_Size(a) else Set_Size(a) + 1);

axiom (forall<T> a: Set T, t: T :: {Set_Remove(a, t)} Set_Size(Set_Remove(a, t)) == if Set_Contains(a, t) then Set_Size(a) - 1 else Set_Size(a));

axiom (forall<T> a: Set T, b: Set T ::
        {Set_Difference(a, b)} {Set_Intersection(a, b)} {Set_Union(a, b)}
        Set_Size(a) == Set_Size(Set_Difference(a, b)) + Set_Size(Set_Intersection(a, b)));

axiom (forall<T> a: Set T, b: Set T ::
        {Set_Union(a, b)} {Set_Intersection(a, b)}
        Set_Size(Set_Union(a, b)) + Set_Size(Set_Intersection(a, b)) == Set_Size(a) + Set_Size(b));

axiom (forall<T> a: Set T, b: Set T :: Set_Union(a, b) == Set_Union(b, a));

axiom (forall<T> a: Set T, b: Set T :: Set_Intersection(a, b) == Set_Intersection(b, a));

function {:inline} Set_Empty<T>(): Set T
{
  Set(MapConst(false))
}

function {:inline} Set_Contains<T>(a: Set T, t: T): bool
{
  a->val[t]
}

function {:inline} Set_IsSubset<T>(a: Set T, b: Set T): bool
{
  Set_Union(a, b) == b
}

function {:inline} Set_IsDisjoint<T>(a: Set T, b: Set T): bool
{
  Set_Intersection(a, b) == Set_Empty()
}

function Set_Add<T>(a: Set T, t: T): Set T
{
  Set(a->val[t := true])
}

function {:inline} Set_Singleton<T>(t: T): Set T
{
  Set_Add(Set_Empty(), t)
}

function Set_Remove<T>(a: Set T, t: T): Set T
{
  Set(a->val[t := false])
}

function Set_Union<T>(a: Set T, b: Set T): Set T
{
  Set(MapOr(a->val, b->val))
}

function Set_Difference<T>(a: Set T, b: Set T): Set T
{
  Set(MapDiff(a->val, b->val))
}

function Set_Intersection<T>(a: Set T, b: Set T): Set T
{
  Set(MapAnd(a->val, b->val))
}

function Choice<T>(a: [T]bool): T;
axiom (forall<T> a: [T]bool :: {Choice(a)} a == MapConst(false) || a[Choice(a)]);

/// finite maps
datatype Map<T,U> {
  Map(dom: Set T, val: [T]U)
}

function {:inline} Map_Contains<T,U>(a: Map T U, t: T): bool
{
    Set_Contains(a->dom, t)
}

function {:inline} Map_At<T,U>(a: Map T U, t: T): U
{
    a->val[t]
}

function {:inline} Map_Remove<T,U>(a: Map T U, t: T): Map T U
{
    Map(Set_Remove(a->dom, t), a->val[t := Default()])
}

function {:inline} Map_Update<T,U>(a: Map T U, t: T, u: U): Map T U
{
    Map(Set_Add(a->dom, t), a->val[t := u])
}

function {:inline} Map_Swap<T,U>(a: Map T U, t1: T, t2: T): Map T U
{
    (var u1, u2 := Map_At(a, t1), Map_At(a, t2); Map_Update(Map_Update(a, t1, u2), t2, u1))
}

/// linear maps
type Loc _;
pure procedure {:inline 1} Loc_New<V>() returns (k: Lval (Loc V)) {

}
datatype Ref<V> {
  Ref(loc: Loc V),
  Nil()
}

datatype Lmap<K,V> { Lmap(dom: [K]bool, val: [K]V) }
type Lheap V = Lmap (Ref V) V;

function {:inline} Lmap_WellFormed<K,V>(l: Lmap K V): bool {
    l->val == MapIte(l->dom, l->val, MapConst(Default()))
}
function {:inline} Lmap_Collector<K,V>(l: Lmap K V): [K]bool {
    l->dom
}
function {:inline} Lmap_Contains<K,V>(l: Lmap K V, k: K): bool {
    l->dom[k]
}
function {:inline} Lmap_Deref<K,V>(l: Lmap K V, k: K): V {
    l->val[k]
}
pure procedure {:inline 1} Lmap_Empty<K,V>() returns (l: Lmap K V) {
  l := Lmap(MapConst(false), MapConst(Default()));
}
pure procedure {:inline 1} Lmap_Alloc<V>(v: V) returns (k: Lval (Loc V), l: Lmap (Ref V) V) {
  var r: Ref V;
  r := Ref(k->val);
  l := Lmap(MapOne(r), MapConst(Default())[r := v]);
}
pure procedure {:inline 1} Lmap_Create<K,V>({:linear_in} k: Lset K, val: [K]V) returns (l: Lmap K V) {
  l := Lmap(k->dom, val);
}
pure procedure {:inline 1} Lmap_Free<K,V>({:linear_in} l: Lmap K V) returns (k: Lset K) {
  k := Lset(l->dom);
}
pure procedure {:inline 1} Lmap_Move<K,V>({:linear_in} src: Lmap K V, dst: Lmap K V, k: K) returns (src': Lmap K V, dst': Lmap K V) {
  assert src->dom[k];
  assume IsDisjoint(src->dom, dst->dom);
  dst' := Lmap(dst->dom[k := true], dst->val[k := src->val[k]]);
  src' := Lmap(src->dom[k := false], src->val[k := Default()]);
}

/// linear sets
datatype Lset<V> { Lset(dom: [V]bool) }

function {:inline} Lset_Collector<V>(l: Lset V): [V]bool {
    l->dom
}
function {:inline} Lset_Contains<V>(l: Lset V, k: V): bool {
    l->dom[k]
}
function {:inline} Lset_IsSubset<V>(k: Lset V, l: Lset V): bool {
    IsSubset(k->dom, l->dom)
}
pure procedure Lset_Empty<V>() returns (l: Lset V);
pure procedure Lset_Split<V>(path: Lset V, {:linear_out} l: Lset V);
pure procedure Lset_Get<V>(path: Lset V, k: [V]bool) returns (l: Lset V);
pure procedure Lset_Put<V>(path: Lset V, {:linear_in} l: Lset V);

/// linear vals
datatype Lval<V> { Lval(val: V) }

function {:inline} Lval_Collector<V>(l: Lval V): [V]bool {
    MapConst(false)[l->val := true]
}
pure procedure Lval_Split<V>(path: Lset V, {:linear_out} l: Lval V);
pure procedure Lval_Get<V>(path: Lset V, k: V) returns (l: Lval V);
pure procedure Lval_Put<V>(path: Lset V, {:linear_in} l: Lval V);

procedure create_async<T>(PA: T);
procedure create_asyncs<T>(PAs: [T]bool);
procedure create_multi_asyncs<T>(PAs: [T]int);
procedure set_choice<T>(choice: T);

pure procedure {:inline 1} Copy<T>(v: T) returns (copy_v: T)
{
  copy_v := v;
}
