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

function {:inline} Id<T>(t: T): T
{
  t
}

function Default<T>(): T;

/// vectors
type {:datatype} Vec _;
function {:constructor} Vec<T>(contents: [int]T, len: int): Vec T;

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

/// linear maps
type Ref _;
type {:datatype} Lmap _;
function {:constructor} Lmap<V>(dom: [Ref V]bool, val: [Ref V]V): Lmap V;

function {:inline} Lmap_WellFormed<V>(l: Lmap V): bool {
    l->val == MapIte(l->dom, l->val, MapConst(Default())) 
}
function {:inline} Lmap_Collector<V>(l: Lmap V): [Ref V]bool {
    l->dom
}
function {:inline} Lmap_Contains<V>(l: Lmap V, k: Ref V): bool {
    l->dom[k]
}
function {:inline} Lmap_Deref<V>(l: Lmap V, k: Ref V): V {
    l->val[k]
}
procedure Lmap_Empty<V>() returns (l: Lmap V);
procedure Lmap_Split<V>(k: [Ref V]bool, path: Lmap V) returns (l: Lmap V);
procedure Lmap_Transfer<V>({:linear_in} path1: Lmap V, path2: Lmap V);
procedure Lmap_Read<V>(path: V) returns (v: V);
procedure Lmap_Write<V>(path: V, v: V);
procedure Lmap_Add<V>(path: Lmap V, v: V) returns (k: Ref V);
procedure Lmap_Remove<V>(path: Lmap V, k: Ref V) returns (v: V);

/// linear sets
type {:datatype} Lset _;
function {:constructor} Lset<V>(dom: [V]bool): Lset V;

function {:inline} Lset_Collector<V>(l: Lset V): [V]bool {
    l->dom
}
function {:inline} Lset_Contains<V>(l: Lset V, k: V): bool {
    l->dom[k]
}
procedure Lset_Empty<V>() returns (l: Lset V);
procedure Lset_Split<V>({:linear_out} k: Lset V, path: Lset V);
procedure Lset_Transfer<V>({:linear_in} path1: Lset V, path2: Lset V);

/// linear vals
type {:datatype} Lval _;
function {:constructor} Lval<V>(val: V): Lval V;

function {:inline} Lval_Collector<V>(l: Lval V): [V]bool {
    MapConst(false)[l->val := true]
}
procedure Lval_Split<V>({:linear_out} k: Lval V, path: Lset V);
procedure Lval_Transfer<V>({:linear_in} l: Lval V, path: Lset V);
