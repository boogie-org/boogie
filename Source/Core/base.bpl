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

function {:inline} IsSet<T>(multiset: [T]int): bool
{
  MapOr(MapEq(multiset, MapConst(0)), MapEq(multiset, MapConst(1))) == MapConst(true)
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

function {:inline} Vec_Concat<T>(v1: Vec T, v2: Vec T): Vec T
{
  Vec(
    (lambda {:pool "Concat"} i: int ::
      if (i < 0) then Default()
      else if (0 <= i && i < Vec_Len(v1)) then Vec_Nth(v1, i)
      else if (Vec_Len(v1) <= i && i < Vec_Len(v1) + Vec_Len(v2)) then Vec_Nth(v2, i - Vec_Len(v1))
      else Default()),
    Vec_Len(v1) + Vec_Len(v2)
  )
}

function {:inline} Vec_Slice<T>(v: Vec T, i: int, j: int): Vec T
{
  (
    var cond := 0 <= i && i < j && j <= v->len;
    Vec(
      (lambda {:pool "Slice"} k: int :: if (cond && 0 <= k && k < j - i) then Vec_Nth(v, k + i) else Default()),
      if (cond) then j - i else 0
    )
  )
}

function {:inline} Vec_Swap<T>(v: Vec T, i: int, j: int): Vec T
{
  (
    var cond := 0 <= i && i < v->len && 0 <= j && j < v->len;
    Vec(v->contents[i := v->contents[if (cond) then j else i]][j := v->contents[if (cond) then i else j]], v->len)
  )
}

function {:inline} Vec_Remove<T>(v: Vec T): Vec T
{
  (
    var cond, new_len := 0 < v->len, v->len - 1;
    Vec(v->contents[new_len := if (cond) then Default() else v->contents[new_len]], if (cond) then new_len else v->len)
  )
}

function {:inline} Vec_Contains<T>(v: Vec T, i: int): bool
{
  0 <= i && i < Vec_Len(v)
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
datatype Set<T> { Set(val: [T]bool) }

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
  IsSubset(a->val, b->val)
}

function {:inline} Set_IsDisjoint<T>(a: Set T, b: Set T): bool
{
  Set_Intersection(a, b) == Set_Empty()
}

function {:inline} Set_Add<T>(a: Set T, t: T): Set T
{
  Set(a->val[t := true])
}

function {:inline} Set_Singleton<T>(t: T): Set T
{
  Set_Add(Set_Empty(), t)
}

function {:inline} Set_Remove<T>(a: Set T, t: T): Set T
{
  Set(a->val[t := false])
}

function {:inline} Set_Union<T>(a: Set T, b: Set T): Set T
{
  Set(MapOr(a->val, b->val))
}

function {:inline} Set_Difference<T>(a: Set T, b: Set T): Set T
{
  Set(MapDiff(a->val, b->val))
}

function {:inline} Set_Intersection<T>(a: Set T, b: Set T): Set T
{
  Set(MapAnd(a->val, b->val))
}

function {:inline} Set_Collector<T>(a: Set T): [T]bool
{
  a->val
}

function Choice<T>(a: [T]bool): T;
axiom (forall<T> a: [T]bool :: {Choice(a)} a == MapConst(false) || a[Choice(a)]);

/// finite maps
datatype Map<T,U> { Map(dom: Set T, val: [T]U) }

function {:inline} Map_Empty<T,U>(): Map T U
{
  Map(Set(MapConst(false)), MapConst(Default()))
}

function {:inline} Map_Singleton<T,U>(t: T, u: U): Map T U
{
  Map_Update(Map_Empty(), t, u)
}

function {:inline} Map_Contains<T,U>(a: Map T U, t: T): bool
{
  Set_Contains(a->dom, t)
}

function {:inline} Map_IsDisjoint<T,U>(a: Map T U, b: Map T U): bool
{
  Set_IsDisjoint(a->dom, b->dom)
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

function {:inline} Map_Extract<T,U>(a: Map T U, t: Set T): Map T U
{
  Map(t, MapIte(t->val, a->val, MapConst(Default())))
}

function {:inline} Map_Exclude<T,U>(a: Map T U, t: Set T): Map T U
{
  Map(Set_Difference(a->dom, t), MapIte(t->val, MapConst(Default()), a->val))
}

function {:inline} Map_Union<T,U>(a: Map T U, b: Map T U): Map T U
{
  Map(Set_Union(a->dom, b->dom), MapIte(a->dom->val, a->val, b->val))
}

function {:inline} Map_WellFormed<T,U>(a: Map T U): bool
{
  a->val == MapIte(a->dom->val, a->val, MapConst(Default()))
}

function {:inline} Map_Collector<T,U>(a: Map T U): [T]bool
{
  Set_Collector(a->dom)
}

/// singleton set
datatype One<T> { One(val: T) }

function {:inline} One_Collector<T>(a: One T): [T]bool
{
  MapOne(a->val)
}

/// singleton map
datatype Cell<T,U> { Cell({:linear} key: One T, val: U) }

function {:inline} Cell_Collector<T,U>(a: Cell T U): [T]bool
{
  MapOne(a->key->val)
}

/// linear primitives
pure procedure {:inline 1} Set_MakeEmpty<K>() returns ({:linear} l: Set K)
{
  l := Set_Empty();
}
pure procedure Set_Split<K>({:linear} path: Set K, {:linear_out} l: Set K);
pure procedure Set_Get<K>({:linear} path: Set K, k: [K]bool) returns ({:linear} l: Set K);
pure procedure Set_Put<K>({:linear} path: Set K, {:linear_in} l: Set K);
pure procedure One_Split<K>({:linear} path: Set K, {:linear_out} l: One K);
pure procedure One_Get<K>({:linear} path: Set K, k: K) returns ({:linear} l: One K);
pure procedure One_Put<K>({:linear} path: Set K, {:linear_in} l: One K);

pure procedure {:inline 1} Map_MakeEmpty<K,V>() returns ({:linear} m: Map K V)
{
  m := Map_Empty();
}
pure procedure {:inline 1} Map_Pack<K,V>({:linear_in} dom: Set K, val: [K]V) returns ({:linear} m: Map K V)
{
  m := Map(dom, MapIte(dom->val, val, MapConst(Default())));
}
pure procedure {:inline 1} Map_Unpack<K,V>({:linear_in} m: Map K V) returns ({:linear} dom: Set K, val: [K]V)
{
  dom := m->dom;
  val := m->val;
}
pure procedure Map_Split<K,V>({:linear} path: Map K V, s: Set K) returns ({:linear} m: Map K V);
pure procedure Map_Join<K,V>({:linear} path: Map K V, {:linear_in} m: Map K V);
pure procedure Map_Get<K,V>({:linear} path: Map K V, k: K) returns ({:linear} l: One K, {:linear} v: V);
pure procedure Map_Put<K,V>({:linear} path: Map K V, {:linear_in} l: One K, {:linear_in} v: V);
pure procedure Map_GetValue<K,V>({:linear} path: Map K V, k: K) returns ({:linear} v: V);
pure procedure Map_PutValue<K,V>({:linear} path: Map K V, k: K, {:linear_in} v: V);

type Loc _;

pure procedure {:inline 1} Loc_New<V>() returns ({:linear} {:pool "Loc_New"} l: One (Loc V))
{
  assume {:add_to_pool "Loc_New", l} true;
}

datatype TaggedLoc<V,T> { TaggedLoc(loc: Loc V, tag: T) }

pure procedure {:inline 1} TaggedLocSet_New<V,T>(tags: Set T) returns ({:linear} {:pool "Loc_New"} l: One (Loc V), {:linear} tagged_locs: Set (TaggedLoc V T))
{
  assume {:add_to_pool "Loc_New", l} true;
  tagged_locs := Set((lambda x: TaggedLoc V T :: x->loc == l->val && Set_Contains(tags, x->tag)));
}

procedure create_async<T>(PA: T);
procedure create_asyncs<T>(PAs: [T]bool);
procedure create_multi_asyncs<T>(PAs: [T]int);
procedure set_choice<T>(choice: T);

pure procedure {:inline 1} Copy<T>(v: T) returns (copy_v: T)
{
  copy_v := v;
}

pure procedure Assume(b: bool);
ensures b;

pure procedure Move<T>({:linear_in} v: T, {:linear_out} v': T);
requires v == v';

datatype Unit { Unit() }
function {:inline} UnitSet(): Set Unit {
  Set_Add(Set_Empty(), Unit())
}
