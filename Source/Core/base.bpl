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

/// wrappers for set operations
function {:inline} Set_Empty<T>(): [T]bool
{
  MapConst(false)
}

function {:inline} Set_Contains<T>(a: [T]bool, t: T): bool
{
  a[t]
}

function {:inline} Set_IsSubset<T>(a: [T]bool, b: [T]bool): bool
{
  MapImp(a, b) == MapConst(true)
}

function {:inline} Set_IsDisjoint<T>(a: [T]bool, b: [T]bool): bool
{
  Set_Intersection(a, b) == Set_Empty()
}

function {:inline} Set_Add<T>(a: [T]bool, t: T): [T]bool
{
  a[t := true]
}

function {:inline} Set_Singleton<T>(t: T): [T]bool
{
  Set_Add(Set_Empty(), t)
}

function {:inline} Set_Remove<T>(a: [T]bool, t: T): [T]bool
{
  a[t := false]
}

function {:inline} Set_Union<T>(a: [T]bool, b: [T]bool): [T]bool
{
  MapOr(a, b)
}

function {:inline} Set_Difference<T>(a: [T]bool, b: [T]bool): [T]bool
{
  MapDiff(a, b)
}

function {:inline} Set_Intersection<T>(a: [T]bool, b: [T]bool): [T]bool
{
  MapAnd(a, b)
}

function Choice<T>(a: [T]bool): T;
axiom (forall<T> a: [T]bool :: {Choice(a)} a == MapConst(false) || a[Choice(a)]);

/// finite maps
datatype Map<T,U> { Map(dom: [T]bool, val: [T]U) }

function {:inline} Map_Empty<T,U>(): Map T U
{
  Map(MapConst(false), MapConst(Default()))
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

function {:inline} Map_Extract<T,U>(a: Map T U, t: [T]bool): Map T U
{
  Map(t, MapIte(t, a->val, MapConst(Default())))
}

function {:inline} Map_Exclude<T,U>(a: Map T U, t: [T]bool): Map T U
{
  Map(Set_Difference(a->dom, t), MapIte(t, MapConst(Default()), a->val))
}

function {:inline} Map_Union<T,U>(a: Map T U, b: Map T U): Map T U
{
  Map(Set_Union(a->dom, b->dom), MapIte(a->dom, a->val, b->val))
}

function {:inline} Map_WellFormed<T,U>(a: Map T U): bool
{
  a->val == MapIte(a->dom, a->val, MapConst(Default()))
}

function {:inline} Map_Collector<T,U>(a: Map T U): [T]bool
{
  a->dom
}

function {:inline} Map_Collector_Empty<T,U,P>(a: Map T U): [P]bool
{
  MapConst(false)
}

/// singleton set
datatype One<T> { One(val: T) }

function {:inline} One_Collector<T>(a: One T): [One T]bool
{
  Set_Singleton(a)
}

/// singleton map
datatype Cell<T,U> { Cell(key: One T, val: U) }

datatype Unit { Unit() }

type UnitMap K = Map K Unit;

/// linear primitives
pure procedure Move<T>({:linear_in} u: T, {:linear_out} v: T);
pure procedure {:inline 1} Map_MakeEmpty<K,V>() returns ({:linear} m: Map K V)
{
  m := Map_Empty();
}
pure procedure One_Get<K>({:linear} path: UnitMap K, {:linear_out} l: K);
pure procedure One_Put<K>({:linear} path: UnitMap K, {:linear_in} l: K);
pure procedure Map_Get<K,V>({:linear} path: Map K V, {:linear_out} k: K) returns ({:linear} v: V);
pure procedure Map_Put<K,V>({:linear} path: Map K V, {:linear_in} k: K, {:linear_in} v: V);
pure procedure Map_Split<K,V>({:linear} path: Map K V, k: [K]bool) returns ({:linear} l: Map K V);
pure procedure Map_Join<K,V>({:linear} path: Map K V, {:linear_in} l: Map K V);
pure procedure Path_Load<V>(path: V) returns (v: V);
pure procedure Path_Store<V>(path: V, v: V);

type Loc;

pure procedure {:inline 1} Loc_New() returns ({:linear} {:pool "Loc_New"} l: One Loc)
{
  assume {:add_to_pool "Loc_New", l} true;
}

datatype Tag<V> { Tag(loc: Loc, val: V) }

pure procedure {:inline 1} Tag_New() returns ({:linear} {:pool "Loc_New"} l: One Loc, {:linear} tag: One (Tag Unit))
{
  assume {:add_to_pool "Loc_New", l} true;
  tag := One(Tag(l->val, Unit()));
}

pure procedure {:inline 1} Tags_New<V>(vals: [V]bool) returns ({:linear} {:pool "Loc_New"} l: One Loc, {:linear} tags: UnitMap (One (Tag V)))
{
  assume {:add_to_pool "Loc_New", l} true;
  tags := Map((lambda x: One (Tag V) :: x->val->loc == l->val && Set_Contains(vals, x->val->val)), MapConst(Unit()));
}

/// Helpers
pure procedure Copy<T>(v: T) returns (v': T);
ensures v' == v;

pure procedure Assume(b: bool);
ensures b;

pure action Assert(b: bool)
{
  assert b;
}
