// Boogie program verifier version 3.2.4.0, Copyright (c) 2003-2014, Microsoft.
// Command Line Options: distributed-snapshot.bpl /civlDesugaredFile:sugar.bpl /keepQuantifier

type Value;

type Tid;

datatype StampedValue {
  StampedValue(ts: int, value: Value)
}

type Channel;

type ChannelPiece = Fraction_5798_5799;

type MemIndexPiece = Fraction_5843_35;

type Snapshot = [int]StampedValue;

datatype ChannelOp {
  Receive(),
  SendFirst(),
  SendSecond()
}

function {:inline} ChannelOps() : Set_5799
{
  Set_Add_4434(Set_Add_4434(Set_Add_4434(Set_Empty_4434(), Receive()), SendFirst()), 
    SendSecond())
}

function {:inline} IsReceive(piece: Fraction_5798_5799) : bool
{
  piece == Fraction_5798_5799(piece->val, Receive(), ChannelOps())
}

function {:inline} IsSendFirst(piece: Fraction_5798_5799) : bool
{
  piece == Fraction_5798_5799(piece->val, SendFirst(), ChannelOps())
}

function {:inline} IsSendSecond(piece: Fraction_5798_5799) : bool
{
  piece == Fraction_5798_5799(piece->val, SendSecond(), ChannelOps())
}

function {:inline} ToReceive(loc_channel: Loc_5796) : Fraction_5798_5799
{
  Fraction_5798_5799(loc_channel, Receive(), ChannelOps())
}

function {:inline} ToSendFirst(loc_channel: Loc_5796) : Fraction_5798_5799
{
  Fraction_5798_5799(loc_channel, SendFirst(), ChannelOps())
}

function {:inline} ToSendSecond(loc_channel: Loc_5796) : Fraction_5798_5799
{
  Fraction_5798_5799(loc_channel, SendSecond(), ChannelOps())
}

const NumMemIndices: int;

function {:inline} MemIndexPieces(s: Fraction_5798_5799, j: int) : Set_6344
{
  Set_6344((lambda {:pool "MemIndexPieces"} x: Fraction_5843_35 :: 
      x->val == s && x->ids == MemIndices() && 1 <= x->id && x->id <= j))
}

function {:inline} AllMemIndexPieces(s: Fraction_5798_5799) : Set_6344
{
  MemIndexPieces(s, NumMemIndices)
}

function {:inline} MemIndices() : Set_35
{
  Set_35((lambda {:pool "MemIndices"} x: int :: 1 <= x && x <= NumMemIndices))
}

function {:inline} IsValidMemIndexPiece(piece: Fraction_5843_35) : bool
{
  Set_Contains_35(piece->ids, piece->id) && piece->ids == MemIndices()
}

function {:inline} MemIndexPiece(cp: Fraction_5798_5799, i: int) : Fraction_5843_35
{
  Fraction_5843_35(cp, i, MemIndices())
}

var mem: [int]StampedValue;

var pset: Map_6774_6775;

datatype write {
  write(i: int, v: Value)
}

datatype main_f' {
  main_f'(s: Fraction_5798_5799, sps: Set_6344)
}

datatype main_f {
  main_f(s: Fraction_5798_5799, sps: Set_6344)
}

datatype read_f {
  read_f(perm: One_12014)
}

datatype main_s' {
  main_s'(s: Fraction_5798_5799, sps: Set_6344)
}

datatype main_s {
  main_s(s: Fraction_5798_5799, sps: Set_6344)
}

datatype read_s {
  read_s(perm: One_12014)
}

const Identity: [int]int;

function {:inline} AtLeast(x: int) : [int]bool
{
  MapLe_2391(MapConst_2408_2391(x), Identity)
}

function {:inline} Range(from: int, n: int) : [int]bool
{
  MapDiff_2411(AtLeast(from), AtLeast(from + n))
}

type {:builtin "Seq"} Seq _;

pure procedure Assume(b: bool);
  ensures b;



type Loc_5796;

datatype Fraction_5798_5799 {
  Fraction_5798_5799(val: Loc_5796, id: ChannelOp, ids: Set_5799)
}

datatype Set_5799 {
  Set_5799(val: [ChannelOp]bool)
}

datatype Fraction_5843_35 {
  Fraction_5843_35(val: Fraction_5798_5799, id: int, ids: Set_35)
}

datatype Set_35 {
  Set_35(val: [int]bool)
}

function {:inline} Set_Empty_4434() : Set_5799
{
  Set_5799(MapConst_5_4434(false))
}

function {:builtin "MapConst"} MapConst_5_4434(bool) : [ChannelOp]bool;

function {:inline} Set_Add_4434(a: Set_5799, t: ChannelOp) : Set_5799
{
  Set_5799(a->val[t := true])
}

datatype Set_6344 {
  Set_6344(val: [Fraction_5843_35]bool)
}

function {:inline} Set_Contains_35(a: Set_35, t: int) : bool
{
  a->val[t]
}

datatype Map_6774_6775 {
  Map_6774_6775(dom: Set_6344, val: [Fraction_5843_35]StampedValue)
}

datatype One_6798 {
  One_6798(val: Loc_5796)
}

datatype Set_6897 {
  Set_6897(val: [Fraction_5798_5799]bool)
}

datatype One_6925 {
  One_6925(val: Fraction_5798_5799)
}

pure procedure {:inline 1} One_To_Fractions_7062_4474(one_t: One_6798, ids: Set_5799) returns (pieces: Set_6897);



function {:inline} AllPieces_7062_4474(t: Loc_5796, ids: Set_5799) : Set_6897
{
  Set_6897((lambda piece: Fraction_5798_5799 :: 
      piece->val == t && Set_Contains_4474(ids, piece->id) && piece->ids == ids))
}

function {:inline} Set_Contains_4474(a: Set_5799, t: ChannelOp) : bool
{
  a->val[t]
}

implementation {:inline 1} One_To_Fractions_7062_4474(one_t: One_6798, ids: Set_5799) returns (pieces: Set_6897)
{

  anon0:
    pieces := AllPieces_7062_4474(one_t->val, ids);
    return;
}



pure procedure One_Get_7285(path: Set_6897, k: Fraction_5798_5799) returns (l: One_6925);



pure procedure {:inline 1} One_To_Fractions_7484_249(one_t: One_6925, ids: Set_35) returns (pieces: Set_6344);



function {:inline} AllPieces_7484_249(t: Fraction_5798_5799, ids: Set_35) : Set_6344
{
  Set_6344((lambda piece: Fraction_5843_35 :: 
      piece->val == t && Set_Contains_35(ids, piece->id) && piece->ids == ids))
}

implementation {:inline 1} One_To_Fractions_7484_249(one_t: One_6925, ids: Set_35) returns (pieces: Set_6344)
{

  anon0:
    pieces := AllPieces_7484_249(one_t->val, ids);
    return;
}



function {:inline} Set_Contains_8465(a: Set_6344, t: Fraction_5843_35) : bool
{
  a->val[t]
}

function {:inline} Map_Contains_8527_4501(a: Map_6774_6775, t: Fraction_5843_35) : bool
{
  Set_Contains_8465(a->dom, t)
}

function {:inline} Map_At_8596_4501(a: Map_6774_6775, t: Fraction_5843_35) : StampedValue
{
  a->val[t]
}

function {:inline} Set_IsSubset_9297(a: Set_6344, b: Set_6344) : bool
{
  IsSubset_9297(a->val, b->val)
}

function {:inline} IsSubset_9297(a: [Fraction_5843_35]bool, b: [Fraction_5843_35]bool) : bool
{
  MapImp_9297(a, b) == MapConst_5_9297(true)
}

function {:builtin "MapImp"} MapImp_9297([Fraction_5843_35]bool, [Fraction_5843_35]bool) : [Fraction_5843_35]bool;

function {:builtin "MapConst"} MapConst_5_9297(bool) : [Fraction_5843_35]bool;

pure procedure Map_Split_9619_4501(path: Map_6774_6775, s: Set_6344) returns (m: Map_6774_6775);



pure procedure {:inline 1} Map_Unpack_9702_4565(m: Map_6774_6775) returns (dom: Set_6344, val: [Fraction_5843_35]StampedValue);



implementation {:inline 1} Map_Unpack_9702_4565(m: Map_6774_6775) returns (dom: Set_6344, val: [Fraction_5843_35]StampedValue)
{

  anon0:
    dom := m->dom;
    val := m->val;
    return;
}



pure procedure {:inline 1} Map_Pack_11504_4635(dom: Set_6344, val: [Fraction_5843_35]StampedValue) returns (m: Map_6774_6775);



function Default_4635() : StampedValue;

function {:builtin "MapConst"} MapConst_4635_11504(StampedValue) : [Fraction_5843_35]StampedValue;

function {:builtin "MapIte"} MapIte_11504_4635([Fraction_5843_35]bool, 
    [Fraction_5843_35]StampedValue, 
    [Fraction_5843_35]StampedValue)
   : [Fraction_5843_35]StampedValue;

implementation {:inline 1} Map_Pack_11504_4635(dom: Set_6344, val: [Fraction_5843_35]StampedValue) returns (m: Map_6774_6775)
{

  anon0:
    m := Map_6774_6775(dom, MapIte_11504_4635(dom->val, val, MapConst_4635_11504(Default_4635())));
    return;
}



pure procedure Map_Join_11673_4501(path: Map_6774_6775, m: Map_6774_6775);



datatype One_12014 {
  One_12014(val: Fraction_5843_35)
}

procedure create_asyncs_4652(PAs: [read_f]bool);



function {:inline} Set_Add_12677(a: Set_6344, t: Fraction_5843_35) : Set_6344
{
  Set_6344(a->val[t := true])
}

datatype Cell_12762_12763 {
  Cell_12762_12763(key: Fraction_5843_35, val: StampedValue)
}

pure procedure {:inline 1} Cell_Pack_12990_4665(l: One_12014, v: StampedValue) returns (c: Cell_12762_12763);



implementation {:inline 1} Cell_Pack_12990_4665(l: One_12014, v: StampedValue) returns (c: Cell_12762_12763)
{

  anon0:
    c := Cell_12762_12763(l->val, v);
    return;
}



pure procedure Map_Put_13105_4501(path: Map_6774_6775, c: Cell_12762_12763);



pure procedure Set_Get_14183(path: Set_6344, k: [Fraction_5843_35]bool) returns (l: Set_6344);



procedure set_choice_4683(choice: read_f);



procedure create_asyncs_4718(PAs: [read_s]bool);



procedure set_choice_4749(choice: read_s);



function {:builtin "MapConst"} MapConst_2408_2391(int) : [int]int;

function {:builtin "MapLe"} MapLe_2391([int]int, [int]int) : [int]bool;

function {:inline} MapDiff_2411(a: [int]bool, b: [int]bool) : [int]bool
{
  MapAnd_2411(a, MapNot_2411(b))
}

function {:builtin "MapNot"} MapNot_2411([int]bool) : [int]bool;

function {:builtin "MapAnd"} MapAnd_2411([int]bool, [int]bool) : [int]bool;

datatype Vec_4635 {
  Vec_4635(contents: [int]StampedValue, len: int)
}

function {:builtin "MapConst"} MapConst_4635_2432(StampedValue) : [int]StampedValue;

function {:builtin "MapIte"} MapIte_2432_4635([int]bool, [int]StampedValue, [int]StampedValue) : [int]StampedValue;

datatype Vec_5 {
  Vec_5(contents: [int]bool, len: int)
}

function Default_5() : bool;

function {:builtin "MapConst"} MapConst_5_2432(bool) : [int]bool;

function {:builtin "MapIte"} MapIte_2432_5([int]bool, [int]bool, [int]bool) : [int]bool;

datatype Vec_2408 {
  Vec_2408(contents: [int]int, len: int)
}

function Default_2408() : int;

function {:builtin "MapIte"} MapIte_2432_2408([int]bool, [int]int, [int]int) : [int]int;

function Choice_4434(a: [ChannelOp]bool) : ChannelOp;

function Choice_9297(a: [Fraction_5843_35]bool) : Fraction_5843_35;

function Choice_2391(a: [int]bool) : int;

axiom NumMemIndices >= 1;

axiom (forall x: int :: Identity[x] == x);

axiom (forall x: Vec_2408 :: 
  { x->len } { x->contents } 
  MapIte_2432_2408(Range(0, x->len), MapConst_2408_2391(Default_2408()), x->contents)
     == MapConst_2408_2391(Default_2408()));

axiom (forall x: Vec_5 :: 
  { x->len } { x->contents } 
  MapIte_2432_5(Range(0, x->len), MapConst_5_2432(Default_5()), x->contents)
     == MapConst_5_2432(Default_5()));

axiom (forall x: Vec_4635 :: 
  { x->len } { x->contents } 
  MapIte_2432_4635(Range(0, x->len), MapConst_4635_2432(Default_4635()), x->contents)
     == MapConst_4635_2432(Default_4635()));

axiom (forall x: Vec_2408 :: { x->len } x->len >= 0);

axiom (forall x: Vec_5 :: { x->len } x->len >= 0);

axiom (forall x: Vec_4635 :: { x->len } x->len >= 0);

axiom (forall a: [int]bool :: 
  { Choice_2391(a) } 
  a == MapConst_5_2432(false) || a[Choice_2391(a)]);

axiom (forall a: [Fraction_5843_35]bool :: 
  { Choice_9297(a) } 
  a == MapConst_5_9297(false) || a[Choice_9297(a)]);

axiom (forall a: [ChannelOp]bool :: 
  { Choice_4434(a) } 
  a == MapConst_5_4434(false) || a[Choice_4434(a)]);

function {:builtin "MapConst"} MapConst_3_5799(int) : [ChannelOp]int;

function {:builtin "MapAnd"} MapAnd_5799([ChannelOp]bool, [ChannelOp]bool) : [ChannelOp]bool;

function {:builtin "MapOr"} MapOr_5799([ChannelOp]bool, [ChannelOp]bool) : [ChannelOp]bool;

function {:builtin "MapImp"} MapImp_5799([ChannelOp]bool, [ChannelOp]bool) : [ChannelOp]bool;

function {:builtin "MapEq"} MapEq_5799_3([ChannelOp]int, [ChannelOp]int) : [ChannelOp]bool;

function {:builtin "MapAdd"} MapAdd_5799([ChannelOp]int, [ChannelOp]int) : [ChannelOp]int;

function {:builtin "MapIte"} MapIte_5799_3([ChannelOp]bool, [ChannelOp]int, [ChannelOp]int) : [ChannelOp]int;

function {:builtin "MapLe"} MapLe_5799([ChannelOp]int, [ChannelOp]int) : [ChannelOp]bool;

function {:inline} Set_Collector_5799(a: Set_5799) : [ChannelOp]bool
{
  a->val
}

function {:builtin "MapConst"} MapConst_3_6344(int) : [Fraction_5843_35]int;

function {:builtin "MapAnd"} MapAnd_6344([Fraction_5843_35]bool, [Fraction_5843_35]bool) : [Fraction_5843_35]bool;

function {:builtin "MapOr"} MapOr_6344([Fraction_5843_35]bool, [Fraction_5843_35]bool) : [Fraction_5843_35]bool;

function {:builtin "MapEq"} MapEq_6344_3([Fraction_5843_35]int, [Fraction_5843_35]int) : [Fraction_5843_35]bool;

function {:builtin "MapAdd"} MapAdd_6344([Fraction_5843_35]int, [Fraction_5843_35]int) : [Fraction_5843_35]int;

function {:builtin "MapIte"} MapIte_6344_3([Fraction_5843_35]bool, [Fraction_5843_35]int, [Fraction_5843_35]int)
   : [Fraction_5843_35]int;

function {:builtin "MapLe"} MapLe_6344([Fraction_5843_35]int, [Fraction_5843_35]int) : [Fraction_5843_35]bool;

function {:inline} Set_Collector_6344(a: Set_6344) : [Fraction_5843_35]bool
{
  a->val
}

function {:builtin "MapOr"} MapOr_35([int]bool, [int]bool) : [int]bool;

function {:builtin "MapImp"} MapImp_35([int]bool, [int]bool) : [int]bool;

function {:builtin "MapEq"} MapEq_35_3([int]int, [int]int) : [int]bool;

function {:builtin "MapAdd"} MapAdd_35([int]int, [int]int) : [int]int;

function {:inline} Set_Collector_35(a: Set_35) : [int]bool
{
  a->val
}

function {:inline} Map_Collector_6774_6775(a: Map_6774_6775) : [Fraction_5843_35]bool
{
  Set_Collector_6344(a->dom)
}

function {:builtin "MapConst"} MapConst_5_6798(bool) : [Loc_5796]bool;

function {:builtin "MapConst"} MapConst_3_6798(int) : [Loc_5796]int;

function {:builtin "MapAnd"} MapAnd_6798([Loc_5796]bool, [Loc_5796]bool) : [Loc_5796]bool;

function {:builtin "MapOr"} MapOr_6798([Loc_5796]bool, [Loc_5796]bool) : [Loc_5796]bool;

function {:builtin "MapImp"} MapImp_6798([Loc_5796]bool, [Loc_5796]bool) : [Loc_5796]bool;

function {:builtin "MapEq"} MapEq_6798_3([Loc_5796]int, [Loc_5796]int) : [Loc_5796]bool;

function {:builtin "MapAdd"} MapAdd_6798([Loc_5796]int, [Loc_5796]int) : [Loc_5796]int;

function {:builtin "MapIte"} MapIte_6798_3([Loc_5796]bool, [Loc_5796]int, [Loc_5796]int) : [Loc_5796]int;

function {:builtin "MapLe"} MapLe_6798([Loc_5796]int, [Loc_5796]int) : [Loc_5796]bool;

function {:inline} One_Collector_6798(a: One_6798) : [Loc_5796]bool
{
  MapOne_6798(a->val)
}

function {:inline} MapOne_6798(t: Loc_5796) : [Loc_5796]bool
{
  MapConst_5_6798(false)[t := true]
}

function {:builtin "MapConst"} MapConst_5_6897(bool) : [Fraction_5798_5799]bool;

function {:builtin "MapConst"} MapConst_3_6897(int) : [Fraction_5798_5799]int;

function {:builtin "MapAnd"} MapAnd_6897([Fraction_5798_5799]bool, [Fraction_5798_5799]bool) : [Fraction_5798_5799]bool;

function {:builtin "MapOr"} MapOr_6897([Fraction_5798_5799]bool, [Fraction_5798_5799]bool) : [Fraction_5798_5799]bool;

function {:builtin "MapImp"} MapImp_6897([Fraction_5798_5799]bool, [Fraction_5798_5799]bool) : [Fraction_5798_5799]bool;

function {:builtin "MapEq"} MapEq_6897_3([Fraction_5798_5799]int, [Fraction_5798_5799]int) : [Fraction_5798_5799]bool;

function {:builtin "MapAdd"} MapAdd_6897([Fraction_5798_5799]int, [Fraction_5798_5799]int) : [Fraction_5798_5799]int;

function {:builtin "MapIte"} MapIte_6897_3([Fraction_5798_5799]bool, [Fraction_5798_5799]int, [Fraction_5798_5799]int)
   : [Fraction_5798_5799]int;

function {:builtin "MapLe"} MapLe_6897([Fraction_5798_5799]int, [Fraction_5798_5799]int) : [Fraction_5798_5799]bool;

function {:inline} Set_Collector_6897(a: Set_6897) : [Fraction_5798_5799]bool
{
  a->val
}

function {:inline} One_Collector_6925(a: One_6925) : [Fraction_5798_5799]bool
{
  MapOne_6925(a->val)
}

function {:inline} MapOne_6925(t: Fraction_5798_5799) : [Fraction_5798_5799]bool
{
  MapConst_5_6897(false)[t := true]
}

function {:inline} One_Collector_12014(a: One_12014) : [Fraction_5843_35]bool
{
  MapOne_12014(a->val)
}

function {:inline} MapOne_12014(t: Fraction_5843_35) : [Fraction_5843_35]bool
{
  MapConst_5_9297(false)[t := true]
}

function {:inline} Collector_read_f_Fraction_5843_35(target: read_f) : [Fraction_5843_35]bool
{
  (if target is read_f
     then MapOr_6344(One_Collector_12014(target->perm), MapConst_5_9297(false))
     else MapConst_5_9297(false))
}

function {:inline} Cell_Collector_12762_12763(a: Cell_12762_12763) : [Fraction_5843_35]bool
{
  MapOne_12014(a->key)
}

function {:inline} Collector_read_s_Fraction_5843_35(target: read_s) : [Fraction_5843_35]bool
{
  (if target is read_s
     then MapOr_6344(One_Collector_12014(target->perm), MapConst_5_9297(false))
     else MapConst_5_9297(false))
}

function {:inline} Map_Extract_9619_4501(a: Map_6774_6775, t: Set_6344) : Map_6774_6775
{
  Map_6774_6775(t, MapIte_11504_4635(t->val, a->val, MapConst_4635_11504(Default_4635())))
}

function {:inline} Map_Exclude_9619_4501(a: Map_6774_6775, t: Set_6344) : Map_6774_6775
{
  Map_6774_6775(Set_Difference_9619(a->dom, t), 
    MapIte_11504_4635(t->val, MapConst_4635_11504(Default_4635()), a->val))
}

function {:inline} Set_Difference_9619(a: Set_6344, b: Set_6344) : Set_6344
{
  Set_6344(MapDiff_9619(a->val, b->val))
}

function {:inline} MapDiff_9619(a: [Fraction_5843_35]bool, b: [Fraction_5843_35]bool) : [Fraction_5843_35]bool
{
  MapAnd_6344(a, MapNot_9619(b))
}

function {:builtin "MapNot"} MapNot_9619([Fraction_5843_35]bool) : [Fraction_5843_35]bool;

function {:inline} Map_Union_11673_4501(a: Map_6774_6775, b: Map_6774_6775) : Map_6774_6775
{
  Map_6774_6775(Set_Union_11673(a->dom, b->dom), MapIte_11504_4635(a->dom->val, a->val, b->val))
}

function {:inline} Set_Union_11673(a: Set_6344, b: Set_6344) : Set_6344
{
  Set_6344(MapOr_6344(a->val, b->val))
}

function {:inline} Map_Update_13105_4501(a: Map_6774_6775, t: Fraction_5843_35, u: StampedValue) : Map_6774_6775
{
  Map_6774_6775(Set_Add_12677(a->dom, t), a->val[t := u])
}

function {:builtin "MapAdd"} MapAdd_21778([write]int, [write]int) : [write]int;

function {:builtin "MapConst"} MapConst_3_21789(int) : [write]int;

function {:builtin "MapIte"} MapIte_21796_3([write]bool, [write]int, [write]int) : [write]int;

function {:builtin "MapAdd"} MapAdd_21810([main_f']int, [main_f']int) : [main_f']int;

function {:builtin "MapConst"} MapConst_3_21821(int) : [main_f']int;

function {:builtin "MapIte"} MapIte_21828_3([main_f']bool, [main_f']int, [main_f']int) : [main_f']int;

function {:builtin "MapAdd"} MapAdd_21842([main_f]int, [main_f]int) : [main_f]int;

function {:builtin "MapConst"} MapConst_3_21853(int) : [main_f]int;

function {:builtin "MapIte"} MapIte_21860_3([main_f]bool, [main_f]int, [main_f]int) : [main_f]int;

function {:builtin "MapAdd"} MapAdd_21874([read_f]int, [read_f]int) : [read_f]int;

function {:builtin "MapConst"} MapConst_3_21885(int) : [read_f]int;

function {:builtin "MapIte"} MapIte_21892_3([read_f]bool, [read_f]int, [read_f]int) : [read_f]int;

function {:builtin "MapAdd"} MapAdd_21906([main_s']int, [main_s']int) : [main_s']int;

function {:builtin "MapConst"} MapConst_3_21917(int) : [main_s']int;

function {:builtin "MapIte"} MapIte_21924_3([main_s']bool, [main_s']int, [main_s']int) : [main_s']int;

function {:builtin "MapAdd"} MapAdd_21938([main_s]int, [main_s]int) : [main_s]int;

function {:builtin "MapConst"} MapConst_3_21949(int) : [main_s]int;

function {:builtin "MapIte"} MapIte_21956_3([main_s]bool, [main_s]int, [main_s]int) : [main_s]int;

function {:builtin "MapAdd"} MapAdd_21970([read_s]int, [read_s]int) : [read_s]int;

function {:builtin "MapConst"} MapConst_3_21981(int) : [read_s]int;

function {:builtin "MapIte"} MapIte_21988_3([read_s]bool, [read_s]int, [read_s]int) : [read_s]int;

function {:inline} Map_WellFormed_6774_6775(a: Map_6774_6775) : bool
{
  a->val
     == MapIte_11504_4635(a->dom->val, a->val, MapConst_4635_11504(Default_4635()))
}

datatype Choice_Inv_f {
  Choice_Inv_f_read_f(read_f: read_f)
}

datatype Choice_Inv_s {
  Choice_Inv_s_read_s(read_s: read_s)
}

function {:inline} Set_Contains_7285(a: Set_6897, t: Fraction_5798_5799) : bool
{
  a->val[t]
}

function {:inline} Set_Remove_7285(a: Set_6897, t: Fraction_5798_5799) : Set_6897
{
  Set_6897(a->val[t := false])
}

function Trigger_ReceiveSecond_map(map: Map_6774_6775) : bool;

function Trigger_ReceiveSecond_data(data: [Fraction_5843_35]StampedValue) : bool;

function Trigger_ReceiveSecond_inline$Map_Unpack_9702_4565$0$m(inline$Map_Unpack_9702_4565$0$m: Map_6774_6775) : bool;

function Trigger_ReceiveSecond_inline$Map_Unpack_9702_4565$0$dom(inline$Map_Unpack_9702_4565$0$dom: Set_6344) : bool;

function Trigger_ReceiveSecond_inline$Map_Unpack_9702_4565$0$val(inline$Map_Unpack_9702_4565$0$val: [Fraction_5843_35]StampedValue) : bool;

function Trigger_ReceiveFirst_map(map: Map_6774_6775) : bool;

function Trigger_ReceiveFirst_data(data: [Fraction_5843_35]StampedValue) : bool;

function Trigger_ReceiveFirst_inline$Map_Unpack_9702_4565$0$m(inline$Map_Unpack_9702_4565$0$m: Map_6774_6775) : bool;

function Trigger_ReceiveFirst_inline$Map_Unpack_9702_4565$0$dom(inline$Map_Unpack_9702_4565$0$dom: Set_6344) : bool;

function Trigger_ReceiveFirst_inline$Map_Unpack_9702_4565$0$val(inline$Map_Unpack_9702_4565$0$val: [Fraction_5843_35]StampedValue) : bool;

function Trigger_write_x(x: StampedValue) : bool;

function Trigger_main_f'_data(data: [Fraction_5843_35]StampedValue) : bool;

function Trigger_main_f'_map(map: Map_6774_6775) : bool;

function Trigger_main_f'_inline$Map_Pack_11504_4635$0$dom(inline$Map_Pack_11504_4635$0$dom: Set_6344) : bool;

function Trigger_main_f'_inline$Map_Pack_11504_4635$0$val(inline$Map_Pack_11504_4635$0$val: [Fraction_5843_35]StampedValue) : bool;

function Trigger_main_f'_inline$Map_Pack_11504_4635$0$m(inline$Map_Pack_11504_4635$0$m: Map_6774_6775) : bool;

function Trigger_read_f_sv(sv: StampedValue) : bool;

function Trigger_read_f_piece(piece: Fraction_5843_35) : bool;

function Trigger_read_f_cell(cell: Cell_12762_12763) : bool;

function Trigger_read_f_inline$Cell_Pack_12990_4665$0$l(inline$Cell_Pack_12990_4665$0$l: One_12014) : bool;

function Trigger_read_f_inline$Cell_Pack_12990_4665$0$v(inline$Cell_Pack_12990_4665$0$v: StampedValue) : bool;

function Trigger_read_f_inline$Cell_Pack_12990_4665$0$c(inline$Cell_Pack_12990_4665$0$c: Cell_12762_12763) : bool;

function Trigger_Inv_f_j(j: int) : bool;

function Trigger_Inv_f_sps'(sps': Set_6344) : bool;

function Trigger_Inv_f_done_set(done_set: Set_6344) : bool;

function Trigger_Inv_f_choice(choice: read_f) : bool;

function Trigger_Inv_f_map(map: Map_6774_6775) : bool;

function Trigger_Inv_f_data(data: [Fraction_5843_35]StampedValue) : bool;

function Trigger_Inv_f_inline$Map_Pack_11504_4635$0$dom(inline$Map_Pack_11504_4635$0$dom: Set_6344) : bool;

function Trigger_Inv_f_inline$Map_Pack_11504_4635$0$val(inline$Map_Pack_11504_4635$0$val: [Fraction_5843_35]StampedValue) : bool;

function Trigger_Inv_f_inline$Map_Pack_11504_4635$0$m(inline$Map_Pack_11504_4635$0$m: Map_6774_6775) : bool;

function Trigger_main_s'_data(data: [Fraction_5843_35]StampedValue) : bool;

function Trigger_main_s'_map(map: Map_6774_6775) : bool;

function Trigger_main_s'_inline$Map_Pack_11504_4635$0$dom(inline$Map_Pack_11504_4635$0$dom: Set_6344) : bool;

function Trigger_main_s'_inline$Map_Pack_11504_4635$0$val(inline$Map_Pack_11504_4635$0$val: [Fraction_5843_35]StampedValue) : bool;

function Trigger_main_s'_inline$Map_Pack_11504_4635$0$m(inline$Map_Pack_11504_4635$0$m: Map_6774_6775) : bool;

function Trigger_read_s_sv(sv: StampedValue) : bool;

function Trigger_read_s_piece(piece: Fraction_5843_35) : bool;

function Trigger_read_s_cell(cell: Cell_12762_12763) : bool;

function Trigger_read_s_inline$Cell_Pack_12990_4665$0$l(inline$Cell_Pack_12990_4665$0$l: One_12014) : bool;

function Trigger_read_s_inline$Cell_Pack_12990_4665$0$v(inline$Cell_Pack_12990_4665$0$v: StampedValue) : bool;

function Trigger_read_s_inline$Cell_Pack_12990_4665$0$c(inline$Cell_Pack_12990_4665$0$c: Cell_12762_12763) : bool;

function Trigger_Inv_s_j(j: int) : bool;

function Trigger_Inv_s_sps'(sps': Set_6344) : bool;

function Trigger_Inv_s_done_set(done_set: Set_6344) : bool;

function Trigger_Inv_s_choice(choice: read_s) : bool;

function Trigger_Inv_s_map(map: Map_6774_6775) : bool;

function Trigger_Inv_s_data(data: [Fraction_5843_35]StampedValue) : bool;

function Trigger_Inv_s_inline$Map_Pack_11504_4635$0$dom(inline$Map_Pack_11504_4635$0$dom: Set_6344) : bool;

function Trigger_Inv_s_inline$Map_Pack_11504_4635$0$val(inline$Map_Pack_11504_4635$0$val: [Fraction_5843_35]StampedValue) : bool;

function Trigger_Inv_s_inline$Map_Pack_11504_4635$0$m(inline$Map_Pack_11504_4635$0$m: Map_6774_6775) : bool;

function Trigger_main_f_data(data: [Fraction_5843_35]StampedValue) : bool;

function Trigger_main_s_data(data: [Fraction_5843_35]StampedValue) : bool;

procedure ReceiveSecond_GateSufficiencyChecker(one_r: One_6925, s: Fraction_5798_5799)
   returns (sps: Set_6344, snapshot: [int]StampedValue);
  requires true;
  requires Map_WellFormed_6774_6775(pset);
  requires one_r->val->val == s->val;
  requires IsReceive(one_r->val);
  requires IsSendSecond(s);
  requires Set_IsSubset_9297(AllMemIndexPieces(s), pset->dom);
  modifies pset;



implementation ReceiveSecond_GateSufficiencyChecker(one_r: One_6925, s: Fraction_5798_5799)
   returns (sps: Set_6344, snapshot: [int]StampedValue)
{
  var map: Map_6774_6775;
  var data: [Fraction_5843_35]StampedValue;
  var inline$Map_Unpack_9702_4565$0$m: Map_6774_6775;
  var inline$Map_Unpack_9702_4565$0$dom: Set_6344;
  var inline$Map_Unpack_9702_4565$0$val: [Fraction_5843_35]StampedValue;

  /*** structured program:
    call map := Map_Split_9619_4501(pset, AllMemIndexPieces(s));
    call sps, data := Map_Unpack_9702_4565(map);
    snapshot := (lambda x: int :: data[Fraction_5843_35(s, x, MemIndices())]);
  **** end structured program */

  anon0:
    assert Set_IsSubset_9297(AllMemIndexPieces(s), pset->dom);
    map := Map_Extract_9619_4501(pset, AllMemIndexPieces(s));
    pset := Map_Exclude_9619_4501(pset, AllMemIndexPieces(s));
    goto inline$Map_Unpack_9702_4565$0$Entry;

  inline$Map_Unpack_9702_4565$0$Entry:
    inline$Map_Unpack_9702_4565$0$m := map;
    havoc inline$Map_Unpack_9702_4565$0$dom, inline$Map_Unpack_9702_4565$0$val;
    goto inline$Map_Unpack_9702_4565$0$anon0;

  inline$Map_Unpack_9702_4565$0$anon0:
    inline$Map_Unpack_9702_4565$0$dom := inline$Map_Unpack_9702_4565$0$m->dom;
    inline$Map_Unpack_9702_4565$0$val := inline$Map_Unpack_9702_4565$0$m->val;
    goto inline$Map_Unpack_9702_4565$0$Return;

  inline$Map_Unpack_9702_4565$0$Return:
    sps := inline$Map_Unpack_9702_4565$0$dom;
    data := inline$Map_Unpack_9702_4565$0$val;
    goto anon0$1;

  anon0$1:
    snapshot := (lambda x: int :: data[Fraction_5843_35(s, x, MemIndices())]);
    return;
}



procedure ReceiveFirst_GateSufficiencyChecker(one_r: One_6925, s: Fraction_5798_5799)
   returns (sps: Set_6344, snapshot: [int]StampedValue);
  requires true;
  requires Map_WellFormed_6774_6775(pset);
  requires one_r->val->val == s->val;
  requires IsReceive(one_r->val);
  requires IsSendFirst(s) || IsSendSecond(s);
  modifies pset;



implementation ReceiveFirst_GateSufficiencyChecker(one_r: One_6925, s: Fraction_5798_5799)
   returns (sps: Set_6344, snapshot: [int]StampedValue)
{
  var map: Map_6774_6775;
  var data: [Fraction_5843_35]StampedValue;
  var inline$Map_Unpack_9702_4565$0$m: Map_6774_6775;
  var inline$Map_Unpack_9702_4565$0$dom: Set_6344;
  var inline$Map_Unpack_9702_4565$0$val: [Fraction_5843_35]StampedValue;

  /*** structured program:
    assume Set_IsSubset_9297(AllMemIndexPieces(s), pset->dom);
    call map := Map_Split_9619_4501(pset, AllMemIndexPieces(s));
    call sps, data := Map_Unpack_9702_4565(map);
    snapshot := (lambda x: int :: data[Fraction_5843_35(s, x, MemIndices())]);
  **** end structured program */

  anon0:
    assume Set_IsSubset_9297(AllMemIndexPieces(s), pset->dom);
    assert Set_IsSubset_9297(AllMemIndexPieces(s), pset->dom);
    map := Map_Extract_9619_4501(pset, AllMemIndexPieces(s));
    pset := Map_Exclude_9619_4501(pset, AllMemIndexPieces(s));
    goto inline$Map_Unpack_9702_4565$0$Entry;

  inline$Map_Unpack_9702_4565$0$Entry:
    inline$Map_Unpack_9702_4565$0$m := map;
    havoc inline$Map_Unpack_9702_4565$0$dom, inline$Map_Unpack_9702_4565$0$val;
    goto inline$Map_Unpack_9702_4565$0$anon0;

  inline$Map_Unpack_9702_4565$0$anon0:
    inline$Map_Unpack_9702_4565$0$dom := inline$Map_Unpack_9702_4565$0$m->dom;
    inline$Map_Unpack_9702_4565$0$val := inline$Map_Unpack_9702_4565$0$m->val;
    goto inline$Map_Unpack_9702_4565$0$Return;

  inline$Map_Unpack_9702_4565$0$Return:
    sps := inline$Map_Unpack_9702_4565$0$dom;
    data := inline$Map_Unpack_9702_4565$0$val;
    goto anon0$1;

  anon0$1:
    snapshot := (lambda x: int :: data[Fraction_5843_35(s, x, MemIndices())]);
    return;
}



procedure main_f'_GateSufficiencyChecker(s: Fraction_5798_5799, sps: Set_6344);
  requires true;
  requires (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
    MapImp_9297(Map_Collector_6774_6775(pset), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
         == MapConst_5_9297(true)
       && MapImp_9297(Set_Collector_6344(sps), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
         == MapConst_5_9297(true));
  requires Map_WellFormed_6774_6775(pset);
  requires IsSendFirst(s);
  requires sps == AllMemIndexPieces(s);
  modifies pset;



implementation main_f'_GateSufficiencyChecker(s: Fraction_5798_5799, sps: Set_6344)
{
  var {:pool "Data"} data: [Fraction_5843_35]StampedValue;
  var map: Map_6774_6775;
  var inline$Map_Pack_11504_4635$0$dom: Set_6344;
  var inline$Map_Pack_11504_4635$0$val: [Fraction_5843_35]StampedValue;
  var inline$Map_Pack_11504_4635$0$m: Map_6774_6775;

  /*** structured program:
    assume {:add_to_pool "MemIndices", 0, NumMemIndices} {:add_to_pool "Data", data} true;
    assume (forall i: int :: 
      1 <= i && i <= NumMemIndices
         ==> (var x := MemIndexPiece(s, i); data[x]->ts < mem[i]->ts || data[x] == mem[i]));
    call map := Map_Pack_11504_4635(sps, data);
    call Map_Join_11673_4501(pset, map);
  **** end structured program */

  anon0:
    assume {:add_to_pool "MemIndices", 0, NumMemIndices} {:add_to_pool "Data", data} true;
    assume (forall i: int :: 
      1 <= i && i <= NumMemIndices
         ==> (var x := MemIndexPiece(s, i); data[x]->ts < mem[i]->ts || data[x] == mem[i]));
    goto inline$Map_Pack_11504_4635$0$Entry;

  inline$Map_Pack_11504_4635$0$Entry:
    inline$Map_Pack_11504_4635$0$dom := sps;
    inline$Map_Pack_11504_4635$0$val := data;
    havoc inline$Map_Pack_11504_4635$0$m;
    goto inline$Map_Pack_11504_4635$0$anon0;

  inline$Map_Pack_11504_4635$0$anon0:
    inline$Map_Pack_11504_4635$0$m := Map_6774_6775(inline$Map_Pack_11504_4635$0$dom, 
      MapIte_11504_4635(inline$Map_Pack_11504_4635$0$dom->val, 
        inline$Map_Pack_11504_4635$0$val, 
        MapConst_4635_11504(Default_4635())));
    goto inline$Map_Pack_11504_4635$0$Return;

  inline$Map_Pack_11504_4635$0$Return:
    map := inline$Map_Pack_11504_4635$0$m;
    goto anon0$1;

  anon0$1:
    pset := Map_Union_11673_4501(pset, map);
    return;
}



procedure read_f_GateSufficiencyChecker(perm: One_12014);
  requires true;
  requires (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
    MapImp_9297(Map_Collector_6774_6775(pset), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
         == MapConst_5_9297(true)
       && MapImp_9297(One_Collector_12014(perm), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
         == MapConst_5_9297(true));
  requires Map_WellFormed_6774_6775(pset);
  requires IsSendFirst(perm->val->val) && IsValidMemIndexPiece(perm->val);
  modifies pset;



implementation read_f_GateSufficiencyChecker(perm: One_12014)
{
  var {:pool "SV_read_f"} sv: StampedValue;
  var piece: Fraction_5843_35;
  var cell: Cell_12762_12763;
  var inline$Cell_Pack_12990_4665$0$l: One_12014;
  var inline$Cell_Pack_12990_4665$0$v: StampedValue;
  var inline$Cell_Pack_12990_4665$0$c: Cell_12762_12763;

  /*** structured program:
    piece := perm->val;
    assume {:add_to_pool "MemIndexPieces", piece} true;
    assume {:add_to_pool "MemIndices", 0, NumMemIndices} true;
    assume {:add_to_pool "SV_read_f", sv, mem[piece->id]} sv->ts < mem[piece->id]->ts || sv == mem[piece->id];
    call cell := Cell_Pack_12990_4665(perm, sv);
    call Map_Put_13105_4501(pset, cell);
    assume {:add_to_pool "Data", pset->val} true;
  **** end structured program */

  anon0:
    piece := perm->val;
    assume {:add_to_pool "MemIndexPieces", piece} true;
    assume {:add_to_pool "MemIndices", 0, NumMemIndices} true;
    assume {:add_to_pool "SV_read_f", sv, mem[piece->id]} sv->ts < mem[piece->id]->ts || sv == mem[piece->id];
    goto inline$Cell_Pack_12990_4665$0$Entry;

  inline$Cell_Pack_12990_4665$0$Entry:
    inline$Cell_Pack_12990_4665$0$l := perm;
    inline$Cell_Pack_12990_4665$0$v := sv;
    havoc inline$Cell_Pack_12990_4665$0$c;
    goto inline$Cell_Pack_12990_4665$0$anon0;

  inline$Cell_Pack_12990_4665$0$anon0:
    inline$Cell_Pack_12990_4665$0$c := Cell_12762_12763(inline$Cell_Pack_12990_4665$0$l->val, inline$Cell_Pack_12990_4665$0$v);
    goto inline$Cell_Pack_12990_4665$0$Return;

  inline$Cell_Pack_12990_4665$0$Return:
    cell := inline$Cell_Pack_12990_4665$0$c;
    goto anon0$1;

  anon0$1:
    assume {:linear} !Map_Contains_8527_4501(pset, cell->key);
    pset := Map_Update_13105_4501(pset, cell->key, cell->val);
    assume {:add_to_pool "Data", pset->val} true;
    return;
}



procedure Inv_f_GateSufficiencyChecker(s: Fraction_5798_5799, sps: Set_6344) returns (Civl_PAs_read_f: [read_f]int);
  requires true;
  requires (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
    MapImp_9297(Map_Collector_6774_6775(pset), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
         == MapConst_5_9297(true)
       && MapImp_9297(Set_Collector_6344(sps), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
         == MapConst_5_9297(true));
  requires Map_WellFormed_6774_6775(pset);
  requires IsSendFirst(s);
  requires sps == AllMemIndexPieces(s);
  modifies pset;



implementation Inv_f_GateSufficiencyChecker(s: Fraction_5798_5799, sps: Set_6344) returns (Civl_PAs_read_f: [read_f]int)
{
  var {:pool "MemIndices"} j: int;
  var sps': Set_6344;
  var done_set: Set_6344;
  var choice: read_f;
  var map: Map_6774_6775;
  var {:pool "Data"} data: [Fraction_5843_35]StampedValue;
  var inline$Map_Pack_11504_4635$0$dom: Set_6344;
  var inline$Map_Pack_11504_4635$0$val: [Fraction_5843_35]StampedValue;
  var inline$Map_Pack_11504_4635$0$m: Map_6774_6775;

  /*** structured program:
    assume {:add_to_pool "MemIndices", 0, j + 1, NumMemIndices} {:add_to_pool "Data", data} 0 <= j && j <= NumMemIndices;
    assume (forall i: int :: 
      1 <= i && i <= j
         ==> (var x := MemIndexPiece(s, i); data[x]->ts < mem[i]->ts || data[x] == mem[i]));
    sps' := sps;
    call done_set := Set_Get_14183(sps', MemIndexPieces(s, j)->val);
    call map := Map_Pack_11504_4635(done_set, data);
    call Map_Join_11673_4501(pset, map);
    if (j < NumMemIndices)
    {
        choice := read_f(One_12014(Fraction_5843_35(s, j + 1, MemIndices())));
        call set_choice(choice);
        assume {:add_to_pool "Read_PAs", choice} true;
        call {:linear sps'} create_asyncs((lambda {:pool "Read_PAs"} pa: read_f :: Set_Contains(sps', pa->perm->val)));
    }
  **** end structured program */

  anon0:
    Civl_PAs_read_f := MapConst_3_21885(0);
    assume {:add_to_pool "MemIndices", 0, j + 1, NumMemIndices} {:add_to_pool "Data", data} 0 <= j && j <= NumMemIndices;
    assume (forall i: int :: 
      1 <= i && i <= j
         ==> (var x := MemIndexPiece(s, i); data[x]->ts < mem[i]->ts || data[x] == mem[i]));
    sps' := sps;
    done_set := Set_6344(MemIndexPieces(s, j)->val);
    assert Set_IsSubset_9297(done_set, sps');
    sps' := Set_Difference_9619(sps', done_set);
    goto inline$Map_Pack_11504_4635$0$Entry;

  inline$Map_Pack_11504_4635$0$Entry:
    inline$Map_Pack_11504_4635$0$dom := done_set;
    inline$Map_Pack_11504_4635$0$val := data;
    havoc inline$Map_Pack_11504_4635$0$m;
    goto inline$Map_Pack_11504_4635$0$anon0;

  inline$Map_Pack_11504_4635$0$anon0:
    inline$Map_Pack_11504_4635$0$m := Map_6774_6775(inline$Map_Pack_11504_4635$0$dom, 
      MapIte_11504_4635(inline$Map_Pack_11504_4635$0$dom->val, 
        inline$Map_Pack_11504_4635$0$val, 
        MapConst_4635_11504(Default_4635())));
    goto inline$Map_Pack_11504_4635$0$Return;

  inline$Map_Pack_11504_4635$0$Return:
    map := inline$Map_Pack_11504_4635$0$m;
    goto anon0$1;

  anon0$1:
    pset := Map_Union_11673_4501(pset, map);
    goto anon2_Then, anon2_Else;

  anon2_Else:
    assume {:partition} NumMemIndices <= j;
    return;

  anon2_Then:
    assume {:partition} j < NumMemIndices;
    choice := read_f(One_12014(Fraction_5843_35(s, j + 1, MemIndices())));
    assume {:add_to_pool "Read_PAs", choice} true;
    assert (forall Civl_pa: read_f :: 
      (lambda {:pool "Read_PAs"} pa: read_f :: Set_Contains_8465(sps', pa->perm->val))[Civl_pa]
         ==> Set_Contains_8465(sps', Civl_pa->perm->val));
    assert (forall Civl_pa1: read_f, Civl_pa2: read_f :: 
      (lambda {:pool "Read_PAs"} pa: read_f :: Set_Contains_8465(sps', pa->perm->val))[Civl_pa1]
           && (lambda {:pool "Read_PAs"} pa: read_f :: Set_Contains_8465(sps', pa->perm->val))[Civl_pa2]
           && Civl_pa1 != Civl_pa2
         ==> Civl_pa1->perm != Civl_pa2->perm);
    Civl_PAs_read_f := MapAdd_21874(Civl_PAs_read_f, 
      MapIte_21892_3((lambda {:pool "Read_PAs"} pa: read_f :: Set_Contains_8465(sps', pa->perm->val)), 
        MapConst_3_21885(1), 
        MapConst_3_21885(0)));
    return;
}



procedure main_s'_GateSufficiencyChecker(s: Fraction_5798_5799, sps: Set_6344);
  requires true;
  requires (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
    MapImp_9297(Map_Collector_6774_6775(pset), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
         == MapConst_5_9297(true)
       && MapImp_9297(Set_Collector_6344(sps), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
         == MapConst_5_9297(true));
  requires Map_WellFormed_6774_6775(pset);
  requires IsSendSecond(s);
  requires sps == AllMemIndexPieces(s);
  modifies pset;



implementation main_s'_GateSufficiencyChecker(s: Fraction_5798_5799, sps: Set_6344)
{
  var {:pool "Data"} data: [Fraction_5843_35]StampedValue;
  var map: Map_6774_6775;
  var inline$Map_Pack_11504_4635$0$dom: Set_6344;
  var inline$Map_Pack_11504_4635$0$val: [Fraction_5843_35]StampedValue;
  var inline$Map_Pack_11504_4635$0$m: Map_6774_6775;

  /*** structured program:
    assume {:add_to_pool "MemIndices", 0, NumMemIndices} {:add_to_pool "Data", data} true;
    assume (forall i: int :: 
      1 <= i && i <= NumMemIndices
         ==> (var x := MemIndexPiece(s, i); data[x]->ts > mem[i]->ts || data[x] == mem[i]));
    call map := Map_Pack_11504_4635(sps, data);
    call Map_Join_11673_4501(pset, map);
  **** end structured program */

  anon0:
    assume {:add_to_pool "MemIndices", 0, NumMemIndices} {:add_to_pool "Data", data} true;
    assume (forall i: int :: 
      1 <= i && i <= NumMemIndices
         ==> (var x := MemIndexPiece(s, i); data[x]->ts > mem[i]->ts || data[x] == mem[i]));
    goto inline$Map_Pack_11504_4635$0$Entry;

  inline$Map_Pack_11504_4635$0$Entry:
    inline$Map_Pack_11504_4635$0$dom := sps;
    inline$Map_Pack_11504_4635$0$val := data;
    havoc inline$Map_Pack_11504_4635$0$m;
    goto inline$Map_Pack_11504_4635$0$anon0;

  inline$Map_Pack_11504_4635$0$anon0:
    inline$Map_Pack_11504_4635$0$m := Map_6774_6775(inline$Map_Pack_11504_4635$0$dom, 
      MapIte_11504_4635(inline$Map_Pack_11504_4635$0$dom->val, 
        inline$Map_Pack_11504_4635$0$val, 
        MapConst_4635_11504(Default_4635())));
    goto inline$Map_Pack_11504_4635$0$Return;

  inline$Map_Pack_11504_4635$0$Return:
    map := inline$Map_Pack_11504_4635$0$m;
    goto anon0$1;

  anon0$1:
    pset := Map_Union_11673_4501(pset, map);
    return;
}



procedure read_s_GateSufficiencyChecker(perm: One_12014);
  requires true;
  requires (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
    MapImp_9297(Map_Collector_6774_6775(pset), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
         == MapConst_5_9297(true)
       && MapImp_9297(One_Collector_12014(perm), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
         == MapConst_5_9297(true));
  requires Map_WellFormed_6774_6775(pset);
  requires {:add_to_pool "SV_read_s", mem[perm->val->id]} IsSendSecond(perm->val->val) && IsValidMemIndexPiece(perm->val);
  modifies pset;



implementation read_s_GateSufficiencyChecker(perm: One_12014)
{
  var {:pool "SV_read_s"} sv: StampedValue;
  var piece: Fraction_5843_35;
  var cell: Cell_12762_12763;
  var inline$Cell_Pack_12990_4665$0$l: One_12014;
  var inline$Cell_Pack_12990_4665$0$v: StampedValue;
  var inline$Cell_Pack_12990_4665$0$c: Cell_12762_12763;

  /*** structured program:
    piece := perm->val;
    assume {:add_to_pool "MemIndexPieces", piece} true;
    assume {:add_to_pool "MemIndices", 0, NumMemIndices} true;
    assume {:add_to_pool "SV_read_s", sv, mem[piece->id]} sv->ts > mem[piece->id]->ts || sv == mem[piece->id];
    call cell := Cell_Pack_12990_4665(perm, sv);
    call Map_Put_13105_4501(pset, cell);
    assume {:add_to_pool "Data", pset->val} true;
  **** end structured program */

  anon0:
    piece := perm->val;
    assume {:add_to_pool "MemIndexPieces", piece} true;
    assume {:add_to_pool "MemIndices", 0, NumMemIndices} true;
    assume {:add_to_pool "SV_read_s", sv, mem[piece->id]} sv->ts > mem[piece->id]->ts || sv == mem[piece->id];
    goto inline$Cell_Pack_12990_4665$0$Entry;

  inline$Cell_Pack_12990_4665$0$Entry:
    inline$Cell_Pack_12990_4665$0$l := perm;
    inline$Cell_Pack_12990_4665$0$v := sv;
    havoc inline$Cell_Pack_12990_4665$0$c;
    goto inline$Cell_Pack_12990_4665$0$anon0;

  inline$Cell_Pack_12990_4665$0$anon0:
    inline$Cell_Pack_12990_4665$0$c := Cell_12762_12763(inline$Cell_Pack_12990_4665$0$l->val, inline$Cell_Pack_12990_4665$0$v);
    goto inline$Cell_Pack_12990_4665$0$Return;

  inline$Cell_Pack_12990_4665$0$Return:
    cell := inline$Cell_Pack_12990_4665$0$c;
    goto anon0$1;

  anon0$1:
    assume {:linear} !Map_Contains_8527_4501(pset, cell->key);
    pset := Map_Update_13105_4501(pset, cell->key, cell->val);
    assume {:add_to_pool "Data", pset->val} true;
    return;
}



procedure Inv_s_GateSufficiencyChecker(s: Fraction_5798_5799, sps: Set_6344) returns (Civl_PAs_read_s: [read_s]int);
  requires true;
  requires (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
    MapImp_9297(Map_Collector_6774_6775(pset), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
         == MapConst_5_9297(true)
       && MapImp_9297(Set_Collector_6344(sps), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
         == MapConst_5_9297(true));
  requires Map_WellFormed_6774_6775(pset);
  requires IsSendSecond(s);
  requires sps == AllMemIndexPieces(s);
  modifies pset;



implementation Inv_s_GateSufficiencyChecker(s: Fraction_5798_5799, sps: Set_6344) returns (Civl_PAs_read_s: [read_s]int)
{
  var {:pool "MemIndices"} j: int;
  var sps': Set_6344;
  var done_set: Set_6344;
  var choice: read_s;
  var map: Map_6774_6775;
  var {:pool "Data"} data: [Fraction_5843_35]StampedValue;
  var inline$Map_Pack_11504_4635$0$dom: Set_6344;
  var inline$Map_Pack_11504_4635$0$val: [Fraction_5843_35]StampedValue;
  var inline$Map_Pack_11504_4635$0$m: Map_6774_6775;

  /*** structured program:
    assume {:add_to_pool "MemIndices", 0, j + 1, NumMemIndices} {:add_to_pool "Data", data} 0 <= j && j <= NumMemIndices;
    assume (forall i: int :: 
      1 <= i && i <= j
         ==> (var x := MemIndexPiece(s, i); data[x]->ts > mem[i]->ts || data[x] == mem[i]));
    sps' := sps;
    call done_set := Set_Get_14183(sps', MemIndexPieces(s, j)->val);
    call map := Map_Pack_11504_4635(done_set, data);
    call Map_Join_11673_4501(pset, map);
    if (j < NumMemIndices)
    {
        choice := read_s(One_12014(Fraction_5843_35(s, j + 1, MemIndices())));
        call set_choice(choice);
        assume {:add_to_pool "Read_PAs", choice} true;
        call {:linear sps'} create_asyncs((lambda {:pool "Read_PAs"} pa: read_s :: Set_Contains(sps', pa->perm->val)));
    }
  **** end structured program */

  anon0:
    Civl_PAs_read_s := MapConst_3_21981(0);
    assume {:add_to_pool "MemIndices", 0, j + 1, NumMemIndices} {:add_to_pool "Data", data} 0 <= j && j <= NumMemIndices;
    assume (forall i: int :: 
      1 <= i && i <= j
         ==> (var x := MemIndexPiece(s, i); data[x]->ts > mem[i]->ts || data[x] == mem[i]));
    sps' := sps;
    done_set := Set_6344(MemIndexPieces(s, j)->val);
    assert Set_IsSubset_9297(done_set, sps');
    sps' := Set_Difference_9619(sps', done_set);
    goto inline$Map_Pack_11504_4635$0$Entry;

  inline$Map_Pack_11504_4635$0$Entry:
    inline$Map_Pack_11504_4635$0$dom := done_set;
    inline$Map_Pack_11504_4635$0$val := data;
    havoc inline$Map_Pack_11504_4635$0$m;
    goto inline$Map_Pack_11504_4635$0$anon0;

  inline$Map_Pack_11504_4635$0$anon0:
    inline$Map_Pack_11504_4635$0$m := Map_6774_6775(inline$Map_Pack_11504_4635$0$dom, 
      MapIte_11504_4635(inline$Map_Pack_11504_4635$0$dom->val, 
        inline$Map_Pack_11504_4635$0$val, 
        MapConst_4635_11504(Default_4635())));
    goto inline$Map_Pack_11504_4635$0$Return;

  inline$Map_Pack_11504_4635$0$Return:
    map := inline$Map_Pack_11504_4635$0$m;
    goto anon0$1;

  anon0$1:
    pset := Map_Union_11673_4501(pset, map);
    goto anon2_Then, anon2_Else;

  anon2_Else:
    assume {:partition} NumMemIndices <= j;
    return;

  anon2_Then:
    assume {:partition} j < NumMemIndices;
    choice := read_s(One_12014(Fraction_5843_35(s, j + 1, MemIndices())));
    assume {:add_to_pool "Read_PAs", choice} true;
    assert (forall Civl_pa: read_s :: 
      (lambda {:pool "Read_PAs"} pa: read_s :: Set_Contains_8465(sps', pa->perm->val))[Civl_pa]
         ==> Set_Contains_8465(sps', Civl_pa->perm->val));
    assert (forall Civl_pa1: read_s, Civl_pa2: read_s :: 
      (lambda {:pool "Read_PAs"} pa: read_s :: Set_Contains_8465(sps', pa->perm->val))[Civl_pa1]
           && (lambda {:pool "Read_PAs"} pa: read_s :: Set_Contains_8465(sps', pa->perm->val))[Civl_pa2]
           && Civl_pa1 != Civl_pa2
         ==> Civl_pa1->perm != Civl_pa2->perm);
    Civl_PAs_read_s := MapAdd_21970(Civl_PAs_read_s, 
      MapIte_21988_3((lambda {:pool "Read_PAs"} pa: read_s :: Set_Contains_8465(sps', pa->perm->val)), 
        MapConst_3_21981(1), 
        MapConst_3_21981(0)));
    return;
}



procedure main_f_GateSufficiencyChecker(s: Fraction_5798_5799, sps: Set_6344) returns (Civl_PAs_read_f: [read_f]int);
  requires true;
  requires IsSendFirst(s);
  requires sps == AllMemIndexPieces(s);



implementation main_f_GateSufficiencyChecker(s: Fraction_5798_5799, sps: Set_6344) returns (Civl_PAs_read_f: [read_f]int)
{
  var data: [Fraction_5843_35]StampedValue;

  /*** structured program:
    assume {:add_to_pool "MemIndices", 0, NumMemIndices} {:add_to_pool "Data", data} true;
    call {:linear sps} create_asyncs_4652((lambda pa: read_f :: Set_Contains_8465(sps, pa->perm->val)));
  **** end structured program */

  anon0:
    Civl_PAs_read_f := MapConst_3_21885(0);
    assume {:add_to_pool "MemIndices", 0, NumMemIndices} {:add_to_pool "Data", data} true;
    assert (forall Civl_pa: read_f :: 
      (lambda pa: read_f :: Set_Contains_8465(sps, pa->perm->val))[Civl_pa]
         ==> Set_Contains_8465(sps, Civl_pa->perm->val));
    assert (forall Civl_pa1: read_f, Civl_pa2: read_f :: 
      (lambda pa: read_f :: Set_Contains_8465(sps, pa->perm->val))[Civl_pa1]
           && (lambda pa: read_f :: Set_Contains_8465(sps, pa->perm->val))[Civl_pa2]
           && Civl_pa1 != Civl_pa2
         ==> Civl_pa1->perm != Civl_pa2->perm);
    Civl_PAs_read_f := MapAdd_21874(Civl_PAs_read_f, 
      MapIte_21892_3((lambda pa: read_f :: Set_Contains_8465(sps, pa->perm->val)), 
        MapConst_3_21885(1), 
        MapConst_3_21885(0)));
    return;
}



procedure main_s_GateSufficiencyChecker(s: Fraction_5798_5799, sps: Set_6344) returns (Civl_PAs_read_s: [read_s]int);
  requires true;
  requires IsSendSecond(s);
  requires sps == AllMemIndexPieces(s);



implementation main_s_GateSufficiencyChecker(s: Fraction_5798_5799, sps: Set_6344) returns (Civl_PAs_read_s: [read_s]int)
{
  var data: [Fraction_5843_35]StampedValue;

  /*** structured program:
    assume {:add_to_pool "MemIndices", 0, NumMemIndices} {:add_to_pool "Data", data} true;
    call {:linear sps} create_asyncs_4718((lambda pa: read_s :: Set_Contains_8465(sps, pa->perm->val)));
  **** end structured program */

  anon0:
    Civl_PAs_read_s := MapConst_3_21981(0);
    assume {:add_to_pool "MemIndices", 0, NumMemIndices} {:add_to_pool "Data", data} true;
    assert (forall Civl_pa: read_s :: 
      (lambda pa: read_s :: Set_Contains_8465(sps, pa->perm->val))[Civl_pa]
         ==> Set_Contains_8465(sps, Civl_pa->perm->val));
    assert (forall Civl_pa1: read_s, Civl_pa2: read_s :: 
      (lambda pa: read_s :: Set_Contains_8465(sps, pa->perm->val))[Civl_pa1]
           && (lambda pa: read_s :: Set_Contains_8465(sps, pa->perm->val))[Civl_pa2]
           && Civl_pa1 != Civl_pa2
         ==> Civl_pa1->perm != Civl_pa2->perm);
    Civl_PAs_read_s := MapAdd_21970(Civl_PAs_read_s, 
      MapIte_21988_3((lambda pa: read_s :: Set_Contains_8465(sps, pa->perm->val)), 
        MapConst_3_21981(1), 
        MapConst_3_21981(0)));
    return;
}



implementation GetSnapshot(one_loc_channel: One_6798) returns (snapshot: [int]StampedValue)
{
  /*** structured program:
    assume (forall i: int :: 1 <= i && i <= NumMemIndices ==> snapshot[i] == mem[i]);
  **** end structured program */

  anon0:
    assume (forall i: int :: 1 <= i && i <= NumMemIndices ==> snapshot[i] == mem[i]);
    return;
}



procedure {:inline 1} GetSnapshot(one_loc_channel: One_6798) returns (snapshot: [int]StampedValue);



function {:inline} Civl_InputOutputRelation_GetSnapshot(one_loc_channel: One_6798, snapshot: [int]StampedValue) : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_pset: Map_6774_6775, 
      Civl_mem: [int]StampedValue, 
      Civl_pset: Map_6774_6775 :: 
    (forall i: int :: 1 <= i && i <= NumMemIndices ==> snapshot[i] == Civl_mem[i]))
}

implementation ReceiveSecond(one_r: One_6925, s: Fraction_5798_5799)
   returns (sps: Set_6344, snapshot: [int]StampedValue)
{
  var map: Map_6774_6775;
  var data: [Fraction_5843_35]StampedValue;
  var inline$Map_Unpack_9702_4565$0$m: Map_6774_6775;
  var inline$Map_Unpack_9702_4565$0$dom: Set_6344;
  var inline$Map_Unpack_9702_4565$0$val: [Fraction_5843_35]StampedValue;

  /*** structured program:
    call map := Map_Split_9619_4501(pset, AllMemIndexPieces(s));
    call sps, data := Map_Unpack_9702_4565(map);
    snapshot := (lambda x: int :: data[Fraction_5843_35(s, x, MemIndices())]);
  **** end structured program */

  anon0:
    map := Map_Extract_9619_4501(pset, AllMemIndexPieces(s));
    pset := Map_Exclude_9619_4501(pset, AllMemIndexPieces(s));
    goto inline$Map_Unpack_9702_4565$0$Entry;

  inline$Map_Unpack_9702_4565$0$Entry:
    inline$Map_Unpack_9702_4565$0$m := map;
    havoc inline$Map_Unpack_9702_4565$0$dom, inline$Map_Unpack_9702_4565$0$val;
    goto inline$Map_Unpack_9702_4565$0$anon0;

  inline$Map_Unpack_9702_4565$0$anon0:
    inline$Map_Unpack_9702_4565$0$dom := inline$Map_Unpack_9702_4565$0$m->dom;
    inline$Map_Unpack_9702_4565$0$val := inline$Map_Unpack_9702_4565$0$m->val;
    goto inline$Map_Unpack_9702_4565$0$Return;

  inline$Map_Unpack_9702_4565$0$Return:
    sps := inline$Map_Unpack_9702_4565$0$dom;
    data := inline$Map_Unpack_9702_4565$0$val;
    goto anon0$1;

  anon0$1:
    snapshot := (lambda x: int :: data[Fraction_5843_35(s, x, MemIndices())]);
    return;
}



procedure {:inline 1} ReceiveSecond(one_r: One_6925, s: Fraction_5798_5799)
   returns (sps: Set_6344, snapshot: [int]StampedValue);
  modifies pset;



function {:inline} Civl_InputOutputRelation_ReceiveSecond(one_r: One_6925, 
    s: Fraction_5798_5799, 
    sps: Set_6344, 
    snapshot: [int]StampedValue)
   : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_pset: Map_6774_6775, 
      Civl_mem: [int]StampedValue, 
      Civl_pset: Map_6774_6775 :: 
    one_r->val->val == s->val
       && IsReceive(one_r->val)
       && IsSendSecond(s)
       && Set_IsSubset_9297(AllMemIndexPieces(s), Civl_old_pset->dom)
       && 
      Civl_pset == Map_Exclude_9619_4501(Civl_old_pset, AllMemIndexPieces(s))
       && sps == Map_Extract_9619_4501(Civl_old_pset, AllMemIndexPieces(s))->dom
       && snapshot
         == (lambda x: int :: 
          Map_Extract_9619_4501(Civl_old_pset, AllMemIndexPieces(s))->val[Fraction_5843_35(s, x, MemIndices())]))
}

implementation ReceiveFirst(one_r: One_6925, s: Fraction_5798_5799)
   returns (sps: Set_6344, snapshot: [int]StampedValue)
{
  var map: Map_6774_6775;
  var data: [Fraction_5843_35]StampedValue;
  var inline$Map_Unpack_9702_4565$0$m: Map_6774_6775;
  var inline$Map_Unpack_9702_4565$0$dom: Set_6344;
  var inline$Map_Unpack_9702_4565$0$val: [Fraction_5843_35]StampedValue;

  /*** structured program:
    assume Set_IsSubset_9297(AllMemIndexPieces(s), pset->dom);
    call map := Map_Split_9619_4501(pset, AllMemIndexPieces(s));
    call sps, data := Map_Unpack_9702_4565(map);
    snapshot := (lambda x: int :: data[Fraction_5843_35(s, x, MemIndices())]);
  **** end structured program */

  anon0:
    assume Set_IsSubset_9297(AllMemIndexPieces(s), pset->dom);
    map := Map_Extract_9619_4501(pset, AllMemIndexPieces(s));
    pset := Map_Exclude_9619_4501(pset, AllMemIndexPieces(s));
    goto inline$Map_Unpack_9702_4565$0$Entry;

  inline$Map_Unpack_9702_4565$0$Entry:
    inline$Map_Unpack_9702_4565$0$m := map;
    havoc inline$Map_Unpack_9702_4565$0$dom, inline$Map_Unpack_9702_4565$0$val;
    goto inline$Map_Unpack_9702_4565$0$anon0;

  inline$Map_Unpack_9702_4565$0$anon0:
    inline$Map_Unpack_9702_4565$0$dom := inline$Map_Unpack_9702_4565$0$m->dom;
    inline$Map_Unpack_9702_4565$0$val := inline$Map_Unpack_9702_4565$0$m->val;
    goto inline$Map_Unpack_9702_4565$0$Return;

  inline$Map_Unpack_9702_4565$0$Return:
    sps := inline$Map_Unpack_9702_4565$0$dom;
    data := inline$Map_Unpack_9702_4565$0$val;
    goto anon0$1;

  anon0$1:
    snapshot := (lambda x: int :: data[Fraction_5843_35(s, x, MemIndices())]);
    return;
}



procedure {:inline 1} ReceiveFirst(one_r: One_6925, s: Fraction_5798_5799)
   returns (sps: Set_6344, snapshot: [int]StampedValue);
  modifies pset;



function {:inline} Civl_InputOutputRelation_ReceiveFirst(one_r: One_6925, 
    s: Fraction_5798_5799, 
    sps: Set_6344, 
    snapshot: [int]StampedValue)
   : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_pset: Map_6774_6775, 
      Civl_mem: [int]StampedValue, 
      Civl_pset: Map_6774_6775 :: 
    one_r->val->val == s->val
       && IsReceive(one_r->val)
       && (IsSendFirst(s) || IsSendSecond(s))
       && 
      Set_IsSubset_9297(AllMemIndexPieces(s), Civl_old_pset->dom)
       && Civl_pset == Map_Exclude_9619_4501(Civl_old_pset, AllMemIndexPieces(s))
       && sps == Map_Extract_9619_4501(Civl_old_pset, AllMemIndexPieces(s))->dom
       && snapshot
         == (lambda x: int :: 
          Map_Extract_9619_4501(Civl_old_pset, AllMemIndexPieces(s))->val[Fraction_5843_35(s, x, MemIndices())]))
}

implementation write(i: int, v: Value)
{
  var x: StampedValue;

  /*** structured program:
    x := mem[i];
    mem[i] := StampedValue(x->ts + 1, v);
  **** end structured program */

  anon0:
    x := mem[i];
    mem[i] := StampedValue(x->ts + 1, v);
    return;
}



procedure {:inline 1} write(i: int, v: Value);
  modifies mem;



function {:inline} Civl_InputOutputRelation_write(i: int, v: Value) : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_pset: Map_6774_6775, 
      Civl_mem: [int]StampedValue, 
      Civl_pset: Map_6774_6775 :: 
    Civl_mem == Civl_old_mem[i := StampedValue(Civl_old_mem[i]->ts + 1, v)])
}

implementation main_f'(s: Fraction_5798_5799, sps: Set_6344)
{
  var {:pool "Data"} data: [Fraction_5843_35]StampedValue;
  var map: Map_6774_6775;
  var inline$Map_Pack_11504_4635$0$dom: Set_6344;
  var inline$Map_Pack_11504_4635$0$val: [Fraction_5843_35]StampedValue;
  var inline$Map_Pack_11504_4635$0$m: Map_6774_6775;

  /*** structured program:
    assume {:add_to_pool "MemIndices", 0, NumMemIndices} {:add_to_pool "Data", data} true;
    assume (forall i: int :: 
      1 <= i && i <= NumMemIndices
         ==> (var x := MemIndexPiece(s, i); data[x]->ts < mem[i]->ts || data[x] == mem[i]));
    call map := Map_Pack_11504_4635(sps, data);
    call Map_Join_11673_4501(pset, map);
  **** end structured program */

  anon0:
    assume Trigger_main_f'_data(data);
    assume {:add_to_pool "MemIndices", 0, NumMemIndices} {:add_to_pool "Data", data} true;
    assume (forall i: int :: 
      1 <= i && i <= NumMemIndices
         ==> (var x := MemIndexPiece(s, i); data[x]->ts < mem[i]->ts || data[x] == mem[i]));
    goto inline$Map_Pack_11504_4635$0$Entry;

  inline$Map_Pack_11504_4635$0$Entry:
    inline$Map_Pack_11504_4635$0$dom := sps;
    inline$Map_Pack_11504_4635$0$val := data;
    havoc inline$Map_Pack_11504_4635$0$m;
    goto inline$Map_Pack_11504_4635$0$anon0;

  inline$Map_Pack_11504_4635$0$anon0:
    inline$Map_Pack_11504_4635$0$m := Map_6774_6775(inline$Map_Pack_11504_4635$0$dom, 
      MapIte_11504_4635(inline$Map_Pack_11504_4635$0$dom->val, 
        inline$Map_Pack_11504_4635$0$val, 
        MapConst_4635_11504(Default_4635())));
    goto inline$Map_Pack_11504_4635$0$Return;

  inline$Map_Pack_11504_4635$0$Return:
    map := inline$Map_Pack_11504_4635$0$m;
    goto anon0$1;

  anon0$1:
    pset := Map_Union_11673_4501(pset, map);
    return;
}



procedure {:inline 1} main_f'(s: Fraction_5798_5799, sps: Set_6344);
  modifies pset;



function {:inline} Civl_InputOutputRelation_main_f'(s: Fraction_5798_5799, sps: Set_6344) : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_pset: Map_6774_6775, 
      Civl_mem: [int]StampedValue, 
      Civl_pset: Map_6774_6775 :: 
    IsSendFirst(s)
       && sps == AllMemIndexPieces(s)
       && (exists {:pool "Data"} Civl_data#0: [Fraction_5843_35]StampedValue :: 
        true
           && (forall i: int :: 
            1 <= i && i <= NumMemIndices
               ==> (var x := MemIndexPiece(s, i); 
                Civl_data#0[x]->ts < Civl_mem[i]->ts || Civl_data#0[x] == Civl_mem[i]))
           && Civl_pset
             == Map_Union_11673_4501(Civl_old_pset, 
              Map_6774_6775(sps, 
                MapIte_11504_4635(sps->val, Civl_data#0, MapConst_4635_11504(Default_4635()))))))
}

implementation read_f(perm: One_12014)
{
  var {:pool "SV_read_f"} sv: StampedValue;
  var piece: Fraction_5843_35;
  var cell: Cell_12762_12763;
  var inline$Cell_Pack_12990_4665$0$l: One_12014;
  var inline$Cell_Pack_12990_4665$0$v: StampedValue;
  var inline$Cell_Pack_12990_4665$0$c: Cell_12762_12763;

  /*** structured program:
    piece := perm->val;
    assume {:add_to_pool "MemIndexPieces", piece} true;
    assume {:add_to_pool "MemIndices", 0, NumMemIndices} true;
    assume {:add_to_pool "SV_read_f", sv, mem[piece->id]} sv->ts < mem[piece->id]->ts || sv == mem[piece->id];
    call cell := Cell_Pack_12990_4665(perm, sv);
    call Map_Put_13105_4501(pset, cell);
    assume {:add_to_pool "Data", pset->val} true;
  **** end structured program */

  anon0:
    assume Trigger_read_f_sv(sv);
    piece := perm->val;
    assume {:add_to_pool "MemIndexPieces", piece} true;
    assume {:add_to_pool "MemIndices", 0, NumMemIndices} true;
    assume {:add_to_pool "SV_read_f", sv, mem[piece->id]} sv->ts < mem[piece->id]->ts || sv == mem[piece->id];
    goto inline$Cell_Pack_12990_4665$0$Entry;

  inline$Cell_Pack_12990_4665$0$Entry:
    inline$Cell_Pack_12990_4665$0$l := perm;
    inline$Cell_Pack_12990_4665$0$v := sv;
    havoc inline$Cell_Pack_12990_4665$0$c;
    goto inline$Cell_Pack_12990_4665$0$anon0;

  inline$Cell_Pack_12990_4665$0$anon0:
    inline$Cell_Pack_12990_4665$0$c := Cell_12762_12763(inline$Cell_Pack_12990_4665$0$l->val, inline$Cell_Pack_12990_4665$0$v);
    goto inline$Cell_Pack_12990_4665$0$Return;

  inline$Cell_Pack_12990_4665$0$Return:
    cell := inline$Cell_Pack_12990_4665$0$c;
    goto anon0$1;

  anon0$1:
    assume {:linear} !Map_Contains_8527_4501(pset, cell->key);
    pset := Map_Update_13105_4501(pset, cell->key, cell->val);
    assume {:add_to_pool "Data", pset->val} true;
    return;
}



procedure {:inline 1} read_f(perm: One_12014);
  modifies pset;



function {:inline} Civl_InputOutputRelation_read_f(perm: One_12014) : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_pset: Map_6774_6775, 
      Civl_mem: [int]StampedValue, 
      Civl_pset: Map_6774_6775 :: 
    IsSendFirst(perm->val->val)
       && IsValidMemIndexPiece(perm->val)
       && (exists {:pool "SV_read_f"} Civl_sv#0: StampedValue :: 
        true
           && true
           && (Civl_sv#0->ts < Civl_mem[perm->val->id]->ts
             || Civl_sv#0 == Civl_mem[perm->val->id])
           && true
           && Civl_pset
             == Map_Update_13105_4501(Civl_old_pset, 
              Cell_12762_12763(perm->val, Civl_sv#0)->key, 
              Cell_12762_12763(perm->val, Civl_sv#0)->val)))
}

implementation Inv_f(s: Fraction_5798_5799, sps: Set_6344) returns (Civl_PAs_read_f: [read_f]int)
{
  var {:pool "MemIndices"} j: int;
  var sps': Set_6344;
  var done_set: Set_6344;
  var choice: read_f;
  var map: Map_6774_6775;
  var {:pool "Data"} data: [Fraction_5843_35]StampedValue;
  var inline$Map_Pack_11504_4635$0$dom: Set_6344;
  var inline$Map_Pack_11504_4635$0$val: [Fraction_5843_35]StampedValue;
  var inline$Map_Pack_11504_4635$0$m: Map_6774_6775;

  /*** structured program:
    assume {:add_to_pool "MemIndices", 0, j + 1, NumMemIndices} {:add_to_pool "Data", data} 0 <= j && j <= NumMemIndices;
    assume (forall i: int :: 
      1 <= i && i <= j
         ==> (var x := MemIndexPiece(s, i); data[x]->ts < mem[i]->ts || data[x] == mem[i]));
    sps' := sps;
    call done_set := Set_Get_14183(sps', MemIndexPieces(s, j)->val);
    call map := Map_Pack_11504_4635(done_set, data);
    call Map_Join_11673_4501(pset, map);
    if (j < NumMemIndices)
    {
        choice := read_f(One_12014(Fraction_5843_35(s, j + 1, MemIndices())));
        call set_choice(choice);
        assume {:add_to_pool "Read_PAs", choice} true;
        call {:linear sps'} create_asyncs((lambda {:pool "Read_PAs"} pa: read_f :: Set_Contains(sps', pa->perm->val)));
    }
  **** end structured program */

  anon0:
    assume Trigger_Inv_f_data(data);
    assume Trigger_Inv_f_j(j);
    Civl_PAs_read_f := MapConst_3_21885(0);
    assume {:add_to_pool "MemIndices", 0, j + 1, NumMemIndices} {:add_to_pool "Data", data} 0 <= j && j <= NumMemIndices;
    assume (forall i: int :: 
      1 <= i && i <= j
         ==> (var x := MemIndexPiece(s, i); data[x]->ts < mem[i]->ts || data[x] == mem[i]));
    sps' := sps;
    done_set := Set_6344(MemIndexPieces(s, j)->val);
    sps' := Set_Difference_9619(sps', done_set);
    goto inline$Map_Pack_11504_4635$0$Entry;

  inline$Map_Pack_11504_4635$0$Entry:
    inline$Map_Pack_11504_4635$0$dom := done_set;
    inline$Map_Pack_11504_4635$0$val := data;
    havoc inline$Map_Pack_11504_4635$0$m;
    goto inline$Map_Pack_11504_4635$0$anon0;

  inline$Map_Pack_11504_4635$0$anon0:
    inline$Map_Pack_11504_4635$0$m := Map_6774_6775(inline$Map_Pack_11504_4635$0$dom, 
      MapIte_11504_4635(inline$Map_Pack_11504_4635$0$dom->val, 
        inline$Map_Pack_11504_4635$0$val, 
        MapConst_4635_11504(Default_4635())));
    goto inline$Map_Pack_11504_4635$0$Return;

  inline$Map_Pack_11504_4635$0$Return:
    map := inline$Map_Pack_11504_4635$0$m;
    goto anon0$1;

  anon0$1:
    pset := Map_Union_11673_4501(pset, map);
    goto anon2_Then, anon2_Else;

  anon2_Else:
    assume {:partition} NumMemIndices <= j;
    return;

  anon2_Then:
    assume {:partition} j < NumMemIndices;
    choice := read_f(One_12014(Fraction_5843_35(s, j + 1, MemIndices())));
    assume {:add_to_pool "Read_PAs", choice} true;
    Civl_PAs_read_f := MapAdd_21874(Civl_PAs_read_f, 
      MapIte_21892_3((lambda {:pool "Read_PAs"} pa: read_f :: Set_Contains_8465(sps', pa->perm->val)), 
        MapConst_3_21885(1), 
        MapConst_3_21885(0)));
    return;
}



procedure {:inline 1} Inv_f(s: Fraction_5798_5799, sps: Set_6344) returns (Civl_PAs_read_f: [read_f]int);
  modifies pset;



function {:inline} Civl_InputOutputRelation_Inv_f(s: Fraction_5798_5799, sps: Set_6344, Civl_PAs_read_f: [read_f]int) : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_pset: Map_6774_6775, 
      Civl_mem: [int]StampedValue, 
      Civl_pset: Map_6774_6775 :: 
    IsSendFirst(s)
       && sps == AllMemIndexPieces(s)
       && ((exists {:pool "MemIndices"} Civl_j#0: int, 
            {:pool "Data"} Civl_data#0: [Fraction_5843_35]StampedValue :: 
          0 <= Civl_j#0
             && Civl_j#0 <= NumMemIndices
             && (forall i: int :: 
              1 <= i && i <= Civl_j#0
                 ==> (var x := MemIndexPiece(s, i); 
                  Civl_data#0[x]->ts < Civl_mem[i]->ts || Civl_data#0[x] == Civl_mem[i]))
             && Civl_j#0 < NumMemIndices
             && true
             && Civl_pset
               == Map_Union_11673_4501(Civl_old_pset, 
                Map_6774_6775(Set_6344(MemIndexPieces(s, Civl_j#0)->val), 
                  MapIte_11504_4635(Set_6344(MemIndexPieces(s, Civl_j#0)->val)->val, 
                    Civl_data#0, 
                    MapConst_4635_11504(Default_4635()))))
             && Civl_PAs_read_f
               == MapAdd_21874(MapConst_3_21885(0), 
                MapIte_21892_3((lambda {:pool "Read_PAs"} pa: read_f :: 
                    Set_Contains_8465(Set_Difference_9619(sps, Set_6344(MemIndexPieces(s, Civl_j#0)->val)), 
                      pa->perm->val)), 
                  MapConst_3_21885(1), 
                  MapConst_3_21885(0))))
         || (exists {:pool "MemIndices"} Civl_j#0: int, 
            {:pool "Data"} Civl_data#0: [Fraction_5843_35]StampedValue :: 
          0 <= Civl_j#0
             && Civl_j#0 <= NumMemIndices
             && (forall i: int :: 
              1 <= i && i <= Civl_j#0
                 ==> (var x := MemIndexPiece(s, i); 
                  Civl_data#0[x]->ts < Civl_mem[i]->ts || Civl_data#0[x] == Civl_mem[i]))
             && NumMemIndices <= Civl_j#0
             && Civl_PAs_read_f == MapConst_3_21885(0)
             && Civl_pset
               == Map_Union_11673_4501(Civl_old_pset, 
                Map_6774_6775(Set_6344(MemIndexPieces(s, Civl_j#0)->val), 
                  MapIte_11504_4635(Set_6344(MemIndexPieces(s, Civl_j#0)->val)->val, 
                    Civl_data#0, 
                    MapConst_4635_11504(Default_4635())))))))
}

implementation Inv_f_With_Choice(s: Fraction_5798_5799, sps: Set_6344)
   returns (Civl_PAs_read_f: [read_f]int, Civl_choice: Choice_Inv_f)
{
  var {:pool "MemIndices"} j: int;
  var sps': Set_6344;
  var done_set: Set_6344;
  var choice: read_f;
  var map: Map_6774_6775;
  var {:pool "Data"} data: [Fraction_5843_35]StampedValue;
  var inline$Map_Pack_11504_4635$0$dom: Set_6344;
  var inline$Map_Pack_11504_4635$0$val: [Fraction_5843_35]StampedValue;
  var inline$Map_Pack_11504_4635$0$m: Map_6774_6775;

  /*** structured program:
    assume {:add_to_pool "MemIndices", 0, j + 1, NumMemIndices} {:add_to_pool "Data", data} 0 <= j && j <= NumMemIndices;
    assume (forall i: int :: 
      1 <= i && i <= j
         ==> (var x := MemIndexPiece(s, i); data[x]->ts < mem[i]->ts || data[x] == mem[i]));
    sps' := sps;
    call done_set := Set_Get_14183(sps', MemIndexPieces(s, j)->val);
    call map := Map_Pack_11504_4635(done_set, data);
    call Map_Join_11673_4501(pset, map);
    if (j < NumMemIndices)
    {
        choice := read_f(One_12014(Fraction_5843_35(s, j + 1, MemIndices())));
        call set_choice(choice);
        assume {:add_to_pool "Read_PAs", choice} true;
        call {:linear sps'} create_asyncs((lambda {:pool "Read_PAs"} pa: read_f :: Set_Contains(sps', pa->perm->val)));
    }
  **** end structured program */

  anon0:
    Civl_PAs_read_f := MapConst_3_21885(0);
    assume {:add_to_pool "MemIndices", 0, j + 1, NumMemIndices} {:add_to_pool "Data", data} 0 <= j && j <= NumMemIndices;
    assume (forall i: int :: 
      1 <= i && i <= j
         ==> (var x := MemIndexPiece(s, i); data[x]->ts < mem[i]->ts || data[x] == mem[i]));
    sps' := sps;
    done_set := Set_6344(MemIndexPieces(s, j)->val);
    assert Set_IsSubset_9297(done_set, sps');
    sps' := Set_Difference_9619(sps', done_set);
    goto inline$Map_Pack_11504_4635$0$Entry;

  inline$Map_Pack_11504_4635$0$Entry:
    inline$Map_Pack_11504_4635$0$dom := done_set;
    inline$Map_Pack_11504_4635$0$val := data;
    havoc inline$Map_Pack_11504_4635$0$m;
    goto inline$Map_Pack_11504_4635$0$anon0;

  inline$Map_Pack_11504_4635$0$anon0:
    inline$Map_Pack_11504_4635$0$m := Map_6774_6775(inline$Map_Pack_11504_4635$0$dom, 
      MapIte_11504_4635(inline$Map_Pack_11504_4635$0$dom->val, 
        inline$Map_Pack_11504_4635$0$val, 
        MapConst_4635_11504(Default_4635())));
    goto inline$Map_Pack_11504_4635$0$Return;

  inline$Map_Pack_11504_4635$0$Return:
    map := inline$Map_Pack_11504_4635$0$m;
    goto anon0$1;

  anon0$1:
    pset := Map_Union_11673_4501(pset, map);
    goto anon2_Then, anon2_Else;

  anon2_Else:
    assume {:partition} NumMemIndices <= j;
    return;

  anon2_Then:
    assume {:partition} j < NumMemIndices;
    choice := read_f(One_12014(Fraction_5843_35(s, j + 1, MemIndices())));
    assert Civl_PAs_read_f == MapConst_3_21885(0) || Civl_PAs_read_f[choice] > 0;
    Civl_choice->read_f := choice;
    assume {:add_to_pool "Read_PAs", choice} true;
    assert (forall Civl_pa: read_f :: 
      (lambda {:pool "Read_PAs"} pa: read_f :: Set_Contains_8465(sps', pa->perm->val))[Civl_pa]
         ==> Set_Contains_8465(sps', Civl_pa->perm->val));
    assert (forall Civl_pa1: read_f, Civl_pa2: read_f :: 
      (lambda {:pool "Read_PAs"} pa: read_f :: Set_Contains_8465(sps', pa->perm->val))[Civl_pa1]
           && (lambda {:pool "Read_PAs"} pa: read_f :: Set_Contains_8465(sps', pa->perm->val))[Civl_pa2]
           && Civl_pa1 != Civl_pa2
         ==> Civl_pa1->perm != Civl_pa2->perm);
    Civl_PAs_read_f := MapAdd_21874(Civl_PAs_read_f, 
      MapIte_21892_3((lambda {:pool "Read_PAs"} pa: read_f :: Set_Contains_8465(sps', pa->perm->val)), 
        MapConst_3_21885(1), 
        MapConst_3_21885(0)));
    return;
}



procedure {:inline 1} Inv_f_With_Choice(s: Fraction_5798_5799, sps: Set_6344)
   returns (Civl_PAs_read_f: [read_f]int, Civl_choice: Choice_Inv_f);
  modifies pset;



function {:inline} Civl_InputOutputRelation_Inv_f_With_Choice(s: Fraction_5798_5799, 
    sps: Set_6344, 
    Civl_PAs_read_f: [read_f]int, 
    Civl_choice: Choice_Inv_f)
   : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_pset: Map_6774_6775, 
      Civl_mem: [int]StampedValue, 
      Civl_pset: Map_6774_6775 :: 
    IsSendFirst(s)
       && sps == AllMemIndexPieces(s)
       && ((exists {:pool "MemIndices"} Civl_j#0: int, 
            {:pool "Data"} Civl_data#0: [Fraction_5843_35]StampedValue :: 
          0 <= Civl_j#0
             && Civl_j#0 <= NumMemIndices
             && (forall i: int :: 
              1 <= i && i <= Civl_j#0
                 ==> (var x := MemIndexPiece(s, i); 
                  Civl_data#0[x]->ts < Civl_mem[i]->ts || Civl_data#0[x] == Civl_mem[i]))
             && Set_IsSubset_9297(Set_6344(MemIndexPieces(s, Civl_j#0)->val), sps)
             && Civl_j#0 < NumMemIndices
             && (MapConst_3_21885(0) == MapConst_3_21885(0)
               || MapConst_3_21885(0)[read_f(One_12014(Fraction_5843_35(s, Civl_j#0 + 1, MemIndices())))]
                 > 0)
             && true
             && (forall Civl_pa: read_f :: 
              (lambda {:pool "Read_PAs"} pa: read_f :: 
                  Set_Contains_8465(Set_Difference_9619(sps, Set_6344(MemIndexPieces(s, Civl_j#0)->val)), 
                    pa->perm->val))[Civl_pa]
                 ==> Set_Contains_8465(Set_Difference_9619(sps, Set_6344(MemIndexPieces(s, Civl_j#0)->val)), 
                  Civl_pa->perm->val))
             && (forall Civl_pa1: read_f, Civl_pa2: read_f :: 
              (lambda {:pool "Read_PAs"} pa: read_f :: 
                    Set_Contains_8465(Set_Difference_9619(sps, Set_6344(MemIndexPieces(s, Civl_j#0)->val)), 
                      pa->perm->val))[Civl_pa1]
                   && (lambda {:pool "Read_PAs"} pa: read_f :: 
                    Set_Contains_8465(Set_Difference_9619(sps, Set_6344(MemIndexPieces(s, Civl_j#0)->val)), 
                      pa->perm->val))[Civl_pa2]
                   && Civl_pa1 != Civl_pa2
                 ==> Civl_pa1->perm != Civl_pa2->perm)
             && Civl_pset
               == Map_Union_11673_4501(Civl_old_pset, 
                Map_6774_6775(Set_6344(MemIndexPieces(s, Civl_j#0)->val), 
                  MapIte_11504_4635(Set_6344(MemIndexPieces(s, Civl_j#0)->val)->val, 
                    Civl_data#0, 
                    MapConst_4635_11504(Default_4635()))))
             && Civl_choice
               == Choice_Inv_f_read_f(read_f(One_12014(Fraction_5843_35(s, Civl_j#0 + 1, MemIndices()))))
             && Civl_PAs_read_f
               == MapAdd_21874(MapConst_3_21885(0), 
                MapIte_21892_3((lambda {:pool "Read_PAs"} pa: read_f :: 
                    Set_Contains_8465(Set_Difference_9619(sps, Set_6344(MemIndexPieces(s, Civl_j#0)->val)), 
                      pa->perm->val)), 
                  MapConst_3_21885(1), 
                  MapConst_3_21885(0))))
         || (exists {:pool "MemIndices"} Civl_j#0: int, 
            {:pool "Data"} Civl_data#0: [Fraction_5843_35]StampedValue :: 
          0 <= Civl_j#0
             && Civl_j#0 <= NumMemIndices
             && (forall i: int :: 
              1 <= i && i <= Civl_j#0
                 ==> (var x := MemIndexPiece(s, i); 
                  Civl_data#0[x]->ts < Civl_mem[i]->ts || Civl_data#0[x] == Civl_mem[i]))
             && Set_IsSubset_9297(Set_6344(MemIndexPieces(s, Civl_j#0)->val), sps)
             && NumMemIndices <= Civl_j#0
             && Civl_PAs_read_f == MapConst_3_21885(0)
             && Civl_pset
               == Map_Union_11673_4501(Civl_old_pset, 
                Map_6774_6775(Set_6344(MemIndexPieces(s, Civl_j#0)->val), 
                  MapIte_11504_4635(Set_6344(MemIndexPieces(s, Civl_j#0)->val)->val, 
                    Civl_data#0, 
                    MapConst_4635_11504(Default_4635())))))))
}

implementation main_s'(s: Fraction_5798_5799, sps: Set_6344)
{
  var {:pool "Data"} data: [Fraction_5843_35]StampedValue;
  var map: Map_6774_6775;
  var inline$Map_Pack_11504_4635$0$dom: Set_6344;
  var inline$Map_Pack_11504_4635$0$val: [Fraction_5843_35]StampedValue;
  var inline$Map_Pack_11504_4635$0$m: Map_6774_6775;

  /*** structured program:
    assume {:add_to_pool "MemIndices", 0, NumMemIndices} {:add_to_pool "Data", data} true;
    assume (forall i: int :: 
      1 <= i && i <= NumMemIndices
         ==> (var x := MemIndexPiece(s, i); data[x]->ts > mem[i]->ts || data[x] == mem[i]));
    call map := Map_Pack_11504_4635(sps, data);
    call Map_Join_11673_4501(pset, map);
  **** end structured program */

  anon0:
    assume Trigger_main_s'_data(data);
    assume {:add_to_pool "MemIndices", 0, NumMemIndices} {:add_to_pool "Data", data} true;
    assume (forall i: int :: 
      1 <= i && i <= NumMemIndices
         ==> (var x := MemIndexPiece(s, i); data[x]->ts > mem[i]->ts || data[x] == mem[i]));
    goto inline$Map_Pack_11504_4635$0$Entry;

  inline$Map_Pack_11504_4635$0$Entry:
    inline$Map_Pack_11504_4635$0$dom := sps;
    inline$Map_Pack_11504_4635$0$val := data;
    havoc inline$Map_Pack_11504_4635$0$m;
    goto inline$Map_Pack_11504_4635$0$anon0;

  inline$Map_Pack_11504_4635$0$anon0:
    inline$Map_Pack_11504_4635$0$m := Map_6774_6775(inline$Map_Pack_11504_4635$0$dom, 
      MapIte_11504_4635(inline$Map_Pack_11504_4635$0$dom->val, 
        inline$Map_Pack_11504_4635$0$val, 
        MapConst_4635_11504(Default_4635())));
    goto inline$Map_Pack_11504_4635$0$Return;

  inline$Map_Pack_11504_4635$0$Return:
    map := inline$Map_Pack_11504_4635$0$m;
    goto anon0$1;

  anon0$1:
    pset := Map_Union_11673_4501(pset, map);
    return;
}



procedure {:inline 1} main_s'(s: Fraction_5798_5799, sps: Set_6344);
  modifies pset;



function {:inline} Civl_InputOutputRelation_main_s'(s: Fraction_5798_5799, sps: Set_6344) : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_pset: Map_6774_6775, 
      Civl_mem: [int]StampedValue, 
      Civl_pset: Map_6774_6775 :: 
    IsSendSecond(s)
       && sps == AllMemIndexPieces(s)
       && (exists {:pool "Data"} Civl_data#0: [Fraction_5843_35]StampedValue :: 
        true
           && (forall i: int :: 
            1 <= i && i <= NumMemIndices
               ==> (var x := MemIndexPiece(s, i); 
                Civl_data#0[x]->ts > Civl_mem[i]->ts || Civl_data#0[x] == Civl_mem[i]))
           && Civl_pset
             == Map_Union_11673_4501(Civl_old_pset, 
              Map_6774_6775(sps, 
                MapIte_11504_4635(sps->val, Civl_data#0, MapConst_4635_11504(Default_4635()))))))
}

implementation read_s(perm: One_12014)
{
  var {:pool "SV_read_s"} sv: StampedValue;
  var piece: Fraction_5843_35;
  var cell: Cell_12762_12763;
  var inline$Cell_Pack_12990_4665$0$l: One_12014;
  var inline$Cell_Pack_12990_4665$0$v: StampedValue;
  var inline$Cell_Pack_12990_4665$0$c: Cell_12762_12763;

  /*** structured program:
    piece := perm->val;
    assume {:add_to_pool "MemIndexPieces", piece} true;
    assume {:add_to_pool "MemIndices", 0, NumMemIndices} true;
    assume {:add_to_pool "SV_read_s", sv, mem[piece->id]} sv->ts > mem[piece->id]->ts || sv == mem[piece->id];
    call cell := Cell_Pack_12990_4665(perm, sv);
    call Map_Put_13105_4501(pset, cell);
    assume {:add_to_pool "Data", pset->val} true;
  **** end structured program */

  anon0:
    assume Trigger_read_s_sv(sv);
    piece := perm->val;
    assume {:add_to_pool "MemIndexPieces", piece} true;
    assume {:add_to_pool "MemIndices", 0, NumMemIndices} true;
    assume {:add_to_pool "SV_read_s", sv, mem[piece->id]} sv->ts > mem[piece->id]->ts || sv == mem[piece->id];
    goto inline$Cell_Pack_12990_4665$0$Entry;

  inline$Cell_Pack_12990_4665$0$Entry:
    inline$Cell_Pack_12990_4665$0$l := perm;
    inline$Cell_Pack_12990_4665$0$v := sv;
    havoc inline$Cell_Pack_12990_4665$0$c;
    goto inline$Cell_Pack_12990_4665$0$anon0;

  inline$Cell_Pack_12990_4665$0$anon0:
    inline$Cell_Pack_12990_4665$0$c := Cell_12762_12763(inline$Cell_Pack_12990_4665$0$l->val, inline$Cell_Pack_12990_4665$0$v);
    goto inline$Cell_Pack_12990_4665$0$Return;

  inline$Cell_Pack_12990_4665$0$Return:
    cell := inline$Cell_Pack_12990_4665$0$c;
    goto anon0$1;

  anon0$1:
    assume {:linear} !Map_Contains_8527_4501(pset, cell->key);
    pset := Map_Update_13105_4501(pset, cell->key, cell->val);
    assume {:add_to_pool "Data", pset->val} true;
    return;
}



procedure {:inline 1} read_s(perm: One_12014);
  modifies pset;



function {:inline} Civl_InputOutputRelation_read_s(perm: One_12014) : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_pset: Map_6774_6775, 
      Civl_mem: [int]StampedValue, 
      Civl_pset: Map_6774_6775 :: 
    IsSendSecond(perm->val->val)
       && IsValidMemIndexPiece(perm->val)
       && (exists {:pool "SV_read_s"} Civl_sv#0: StampedValue :: 
        true
           && true
           && (Civl_sv#0->ts > Civl_mem[perm->val->id]->ts
             || Civl_sv#0 == Civl_mem[perm->val->id])
           && true
           && Civl_pset
             == Map_Update_13105_4501(Civl_old_pset, 
              Cell_12762_12763(perm->val, Civl_sv#0)->key, 
              Cell_12762_12763(perm->val, Civl_sv#0)->val)))
}

implementation Inv_s(s: Fraction_5798_5799, sps: Set_6344) returns (Civl_PAs_read_s: [read_s]int)
{
  var {:pool "MemIndices"} j: int;
  var sps': Set_6344;
  var done_set: Set_6344;
  var choice: read_s;
  var map: Map_6774_6775;
  var {:pool "Data"} data: [Fraction_5843_35]StampedValue;
  var inline$Map_Pack_11504_4635$0$dom: Set_6344;
  var inline$Map_Pack_11504_4635$0$val: [Fraction_5843_35]StampedValue;
  var inline$Map_Pack_11504_4635$0$m: Map_6774_6775;

  /*** structured program:
    assume {:add_to_pool "MemIndices", 0, j + 1, NumMemIndices} {:add_to_pool "Data", data} 0 <= j && j <= NumMemIndices;
    assume (forall i: int :: 
      1 <= i && i <= j
         ==> (var x := MemIndexPiece(s, i); data[x]->ts > mem[i]->ts || data[x] == mem[i]));
    sps' := sps;
    call done_set := Set_Get_14183(sps', MemIndexPieces(s, j)->val);
    call map := Map_Pack_11504_4635(done_set, data);
    call Map_Join_11673_4501(pset, map);
    if (j < NumMemIndices)
    {
        choice := read_s(One_12014(Fraction_5843_35(s, j + 1, MemIndices())));
        call set_choice(choice);
        assume {:add_to_pool "Read_PAs", choice} true;
        call {:linear sps'} create_asyncs((lambda {:pool "Read_PAs"} pa: read_s :: Set_Contains(sps', pa->perm->val)));
    }
  **** end structured program */

  anon0:
    assume Trigger_Inv_s_data(data);
    assume Trigger_Inv_s_j(j);
    Civl_PAs_read_s := MapConst_3_21981(0);
    assume {:add_to_pool "MemIndices", 0, j + 1, NumMemIndices} {:add_to_pool "Data", data} 0 <= j && j <= NumMemIndices;
    assume (forall i: int :: 
      1 <= i && i <= j
         ==> (var x := MemIndexPiece(s, i); data[x]->ts > mem[i]->ts || data[x] == mem[i]));
    sps' := sps;
    done_set := Set_6344(MemIndexPieces(s, j)->val);
    sps' := Set_Difference_9619(sps', done_set);
    goto inline$Map_Pack_11504_4635$0$Entry;

  inline$Map_Pack_11504_4635$0$Entry:
    inline$Map_Pack_11504_4635$0$dom := done_set;
    inline$Map_Pack_11504_4635$0$val := data;
    havoc inline$Map_Pack_11504_4635$0$m;
    goto inline$Map_Pack_11504_4635$0$anon0;

  inline$Map_Pack_11504_4635$0$anon0:
    inline$Map_Pack_11504_4635$0$m := Map_6774_6775(inline$Map_Pack_11504_4635$0$dom, 
      MapIte_11504_4635(inline$Map_Pack_11504_4635$0$dom->val, 
        inline$Map_Pack_11504_4635$0$val, 
        MapConst_4635_11504(Default_4635())));
    goto inline$Map_Pack_11504_4635$0$Return;

  inline$Map_Pack_11504_4635$0$Return:
    map := inline$Map_Pack_11504_4635$0$m;
    goto anon0$1;

  anon0$1:
    pset := Map_Union_11673_4501(pset, map);
    goto anon2_Then, anon2_Else;

  anon2_Else:
    assume {:partition} NumMemIndices <= j;
    return;

  anon2_Then:
    assume {:partition} j < NumMemIndices;
    choice := read_s(One_12014(Fraction_5843_35(s, j + 1, MemIndices())));
    assume {:add_to_pool "Read_PAs", choice} true;
    Civl_PAs_read_s := MapAdd_21970(Civl_PAs_read_s, 
      MapIte_21988_3((lambda {:pool "Read_PAs"} pa: read_s :: Set_Contains_8465(sps', pa->perm->val)), 
        MapConst_3_21981(1), 
        MapConst_3_21981(0)));
    return;
}



procedure {:inline 1} Inv_s(s: Fraction_5798_5799, sps: Set_6344) returns (Civl_PAs_read_s: [read_s]int);
  modifies pset;



function {:inline} Civl_InputOutputRelation_Inv_s(s: Fraction_5798_5799, sps: Set_6344, Civl_PAs_read_s: [read_s]int) : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_pset: Map_6774_6775, 
      Civl_mem: [int]StampedValue, 
      Civl_pset: Map_6774_6775 :: 
    IsSendSecond(s)
       && sps == AllMemIndexPieces(s)
       && ((exists {:pool "MemIndices"} Civl_j#0: int, 
            {:pool "Data"} Civl_data#0: [Fraction_5843_35]StampedValue :: 
          0 <= Civl_j#0
             && Civl_j#0 <= NumMemIndices
             && (forall i: int :: 
              1 <= i && i <= Civl_j#0
                 ==> (var x := MemIndexPiece(s, i); 
                  Civl_data#0[x]->ts > Civl_mem[i]->ts || Civl_data#0[x] == Civl_mem[i]))
             && Civl_j#0 < NumMemIndices
             && true
             && Civl_pset
               == Map_Union_11673_4501(Civl_old_pset, 
                Map_6774_6775(Set_6344(MemIndexPieces(s, Civl_j#0)->val), 
                  MapIte_11504_4635(Set_6344(MemIndexPieces(s, Civl_j#0)->val)->val, 
                    Civl_data#0, 
                    MapConst_4635_11504(Default_4635()))))
             && Civl_PAs_read_s
               == MapAdd_21970(MapConst_3_21981(0), 
                MapIte_21988_3((lambda {:pool "Read_PAs"} pa: read_s :: 
                    Set_Contains_8465(Set_Difference_9619(sps, Set_6344(MemIndexPieces(s, Civl_j#0)->val)), 
                      pa->perm->val)), 
                  MapConst_3_21981(1), 
                  MapConst_3_21981(0))))
         || (exists {:pool "MemIndices"} Civl_j#0: int, 
            {:pool "Data"} Civl_data#0: [Fraction_5843_35]StampedValue :: 
          0 <= Civl_j#0
             && Civl_j#0 <= NumMemIndices
             && (forall i: int :: 
              1 <= i && i <= Civl_j#0
                 ==> (var x := MemIndexPiece(s, i); 
                  Civl_data#0[x]->ts > Civl_mem[i]->ts || Civl_data#0[x] == Civl_mem[i]))
             && NumMemIndices <= Civl_j#0
             && Civl_PAs_read_s == MapConst_3_21981(0)
             && Civl_pset
               == Map_Union_11673_4501(Civl_old_pset, 
                Map_6774_6775(Set_6344(MemIndexPieces(s, Civl_j#0)->val), 
                  MapIte_11504_4635(Set_6344(MemIndexPieces(s, Civl_j#0)->val)->val, 
                    Civl_data#0, 
                    MapConst_4635_11504(Default_4635())))))))
}

implementation Inv_s_With_Choice(s: Fraction_5798_5799, sps: Set_6344)
   returns (Civl_PAs_read_s: [read_s]int, Civl_choice: Choice_Inv_s)
{
  var {:pool "MemIndices"} j: int;
  var sps': Set_6344;
  var done_set: Set_6344;
  var choice: read_s;
  var map: Map_6774_6775;
  var {:pool "Data"} data: [Fraction_5843_35]StampedValue;
  var inline$Map_Pack_11504_4635$0$dom: Set_6344;
  var inline$Map_Pack_11504_4635$0$val: [Fraction_5843_35]StampedValue;
  var inline$Map_Pack_11504_4635$0$m: Map_6774_6775;

  /*** structured program:
    assume {:add_to_pool "MemIndices", 0, j + 1, NumMemIndices} {:add_to_pool "Data", data} 0 <= j && j <= NumMemIndices;
    assume (forall i: int :: 
      1 <= i && i <= j
         ==> (var x := MemIndexPiece(s, i); data[x]->ts > mem[i]->ts || data[x] == mem[i]));
    sps' := sps;
    call done_set := Set_Get_14183(sps', MemIndexPieces(s, j)->val);
    call map := Map_Pack_11504_4635(done_set, data);
    call Map_Join_11673_4501(pset, map);
    if (j < NumMemIndices)
    {
        choice := read_s(One_12014(Fraction_5843_35(s, j + 1, MemIndices())));
        call set_choice(choice);
        assume {:add_to_pool "Read_PAs", choice} true;
        call {:linear sps'} create_asyncs((lambda {:pool "Read_PAs"} pa: read_s :: Set_Contains(sps', pa->perm->val)));
    }
  **** end structured program */

  anon0:
    Civl_PAs_read_s := MapConst_3_21981(0);
    assume {:add_to_pool "MemIndices", 0, j + 1, NumMemIndices} {:add_to_pool "Data", data} 0 <= j && j <= NumMemIndices;
    assume (forall i: int :: 
      1 <= i && i <= j
         ==> (var x := MemIndexPiece(s, i); data[x]->ts > mem[i]->ts || data[x] == mem[i]));
    sps' := sps;
    done_set := Set_6344(MemIndexPieces(s, j)->val);
    assert Set_IsSubset_9297(done_set, sps');
    sps' := Set_Difference_9619(sps', done_set);
    goto inline$Map_Pack_11504_4635$0$Entry;

  inline$Map_Pack_11504_4635$0$Entry:
    inline$Map_Pack_11504_4635$0$dom := done_set;
    inline$Map_Pack_11504_4635$0$val := data;
    havoc inline$Map_Pack_11504_4635$0$m;
    goto inline$Map_Pack_11504_4635$0$anon0;

  inline$Map_Pack_11504_4635$0$anon0:
    inline$Map_Pack_11504_4635$0$m := Map_6774_6775(inline$Map_Pack_11504_4635$0$dom, 
      MapIte_11504_4635(inline$Map_Pack_11504_4635$0$dom->val, 
        inline$Map_Pack_11504_4635$0$val, 
        MapConst_4635_11504(Default_4635())));
    goto inline$Map_Pack_11504_4635$0$Return;

  inline$Map_Pack_11504_4635$0$Return:
    map := inline$Map_Pack_11504_4635$0$m;
    goto anon0$1;

  anon0$1:
    pset := Map_Union_11673_4501(pset, map);
    goto anon2_Then, anon2_Else;

  anon2_Else:
    assume {:partition} NumMemIndices <= j;
    return;

  anon2_Then:
    assume {:partition} j < NumMemIndices;
    choice := read_s(One_12014(Fraction_5843_35(s, j + 1, MemIndices())));
    assert Civl_PAs_read_s == MapConst_3_21981(0) || Civl_PAs_read_s[choice] > 0;
    Civl_choice->read_s := choice;
    assume {:add_to_pool "Read_PAs", choice} true;
    assert (forall Civl_pa: read_s :: 
      (lambda {:pool "Read_PAs"} pa: read_s :: Set_Contains_8465(sps', pa->perm->val))[Civl_pa]
         ==> Set_Contains_8465(sps', Civl_pa->perm->val));
    assert (forall Civl_pa1: read_s, Civl_pa2: read_s :: 
      (lambda {:pool "Read_PAs"} pa: read_s :: Set_Contains_8465(sps', pa->perm->val))[Civl_pa1]
           && (lambda {:pool "Read_PAs"} pa: read_s :: Set_Contains_8465(sps', pa->perm->val))[Civl_pa2]
           && Civl_pa1 != Civl_pa2
         ==> Civl_pa1->perm != Civl_pa2->perm);
    Civl_PAs_read_s := MapAdd_21970(Civl_PAs_read_s, 
      MapIte_21988_3((lambda {:pool "Read_PAs"} pa: read_s :: Set_Contains_8465(sps', pa->perm->val)), 
        MapConst_3_21981(1), 
        MapConst_3_21981(0)));
    return;
}



procedure {:inline 1} Inv_s_With_Choice(s: Fraction_5798_5799, sps: Set_6344)
   returns (Civl_PAs_read_s: [read_s]int, Civl_choice: Choice_Inv_s);
  modifies pset;



function {:inline} Civl_InputOutputRelation_Inv_s_With_Choice(s: Fraction_5798_5799, 
    sps: Set_6344, 
    Civl_PAs_read_s: [read_s]int, 
    Civl_choice: Choice_Inv_s)
   : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_pset: Map_6774_6775, 
      Civl_mem: [int]StampedValue, 
      Civl_pset: Map_6774_6775 :: 
    IsSendSecond(s)
       && sps == AllMemIndexPieces(s)
       && ((exists {:pool "MemIndices"} Civl_j#0: int, 
            {:pool "Data"} Civl_data#0: [Fraction_5843_35]StampedValue :: 
          0 <= Civl_j#0
             && Civl_j#0 <= NumMemIndices
             && (forall i: int :: 
              1 <= i && i <= Civl_j#0
                 ==> (var x := MemIndexPiece(s, i); 
                  Civl_data#0[x]->ts > Civl_mem[i]->ts || Civl_data#0[x] == Civl_mem[i]))
             && Set_IsSubset_9297(Set_6344(MemIndexPieces(s, Civl_j#0)->val), sps)
             && Civl_j#0 < NumMemIndices
             && (MapConst_3_21981(0) == MapConst_3_21981(0)
               || MapConst_3_21981(0)[read_s(One_12014(Fraction_5843_35(s, Civl_j#0 + 1, MemIndices())))]
                 > 0)
             && true
             && (forall Civl_pa: read_s :: 
              (lambda {:pool "Read_PAs"} pa: read_s :: 
                  Set_Contains_8465(Set_Difference_9619(sps, Set_6344(MemIndexPieces(s, Civl_j#0)->val)), 
                    pa->perm->val))[Civl_pa]
                 ==> Set_Contains_8465(Set_Difference_9619(sps, Set_6344(MemIndexPieces(s, Civl_j#0)->val)), 
                  Civl_pa->perm->val))
             && (forall Civl_pa1: read_s, Civl_pa2: read_s :: 
              (lambda {:pool "Read_PAs"} pa: read_s :: 
                    Set_Contains_8465(Set_Difference_9619(sps, Set_6344(MemIndexPieces(s, Civl_j#0)->val)), 
                      pa->perm->val))[Civl_pa1]
                   && (lambda {:pool "Read_PAs"} pa: read_s :: 
                    Set_Contains_8465(Set_Difference_9619(sps, Set_6344(MemIndexPieces(s, Civl_j#0)->val)), 
                      pa->perm->val))[Civl_pa2]
                   && Civl_pa1 != Civl_pa2
                 ==> Civl_pa1->perm != Civl_pa2->perm)
             && Civl_pset
               == Map_Union_11673_4501(Civl_old_pset, 
                Map_6774_6775(Set_6344(MemIndexPieces(s, Civl_j#0)->val), 
                  MapIte_11504_4635(Set_6344(MemIndexPieces(s, Civl_j#0)->val)->val, 
                    Civl_data#0, 
                    MapConst_4635_11504(Default_4635()))))
             && Civl_choice
               == Choice_Inv_s_read_s(read_s(One_12014(Fraction_5843_35(s, Civl_j#0 + 1, MemIndices()))))
             && Civl_PAs_read_s
               == MapAdd_21970(MapConst_3_21981(0), 
                MapIte_21988_3((lambda {:pool "Read_PAs"} pa: read_s :: 
                    Set_Contains_8465(Set_Difference_9619(sps, Set_6344(MemIndexPieces(s, Civl_j#0)->val)), 
                      pa->perm->val)), 
                  MapConst_3_21981(1), 
                  MapConst_3_21981(0))))
         || (exists {:pool "MemIndices"} Civl_j#0: int, 
            {:pool "Data"} Civl_data#0: [Fraction_5843_35]StampedValue :: 
          0 <= Civl_j#0
             && Civl_j#0 <= NumMemIndices
             && (forall i: int :: 
              1 <= i && i <= Civl_j#0
                 ==> (var x := MemIndexPiece(s, i); 
                  Civl_data#0[x]->ts > Civl_mem[i]->ts || Civl_data#0[x] == Civl_mem[i]))
             && Set_IsSubset_9297(Set_6344(MemIndexPieces(s, Civl_j#0)->val), sps)
             && NumMemIndices <= Civl_j#0
             && Civl_PAs_read_s == MapConst_3_21981(0)
             && Civl_pset
               == Map_Union_11673_4501(Civl_old_pset, 
                Map_6774_6775(Set_6344(MemIndexPieces(s, Civl_j#0)->val), 
                  MapIte_11504_4635(Set_6344(MemIndexPieces(s, Civl_j#0)->val)->val, 
                    Civl_data#0, 
                    MapConst_4635_11504(Default_4635())))))))
}

implementation Civl_Skip()
{

  init:
    return;
}



pure procedure {:inline 1} Civl_Skip();



function {:inline} Civl_InputOutputRelation_Civl_Skip() : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_pset: Map_6774_6775, 
      Civl_mem: [int]StampedValue, 
      Civl_pset: Map_6774_6775 :: 
    true)
}

implementation main_f(s: Fraction_5798_5799, sps: Set_6344) returns (Civl_PAs_read_f: [read_f]int)
{
  var data: [Fraction_5843_35]StampedValue;

  /*** structured program:
    assume {:add_to_pool "MemIndices", 0, NumMemIndices} {:add_to_pool "Data", data} true;
    call {:linear sps} create_asyncs_4652((lambda pa: read_f :: Set_Contains_8465(sps, pa->perm->val)));
  **** end structured program */

  anon0:
    Civl_PAs_read_f := MapConst_3_21885(0);
    assume {:add_to_pool "MemIndices", 0, NumMemIndices} {:add_to_pool "Data", data} true;
    Civl_PAs_read_f := MapAdd_21874(Civl_PAs_read_f, 
      MapIte_21892_3((lambda pa: read_f :: Set_Contains_8465(sps, pa->perm->val)), 
        MapConst_3_21885(1), 
        MapConst_3_21885(0)));
    return;
}



procedure {:inline 1} main_f(s: Fraction_5798_5799, sps: Set_6344) returns (Civl_PAs_read_f: [read_f]int);



function {:inline} Civl_InputOutputRelation_main_f(s: Fraction_5798_5799, sps: Set_6344, Civl_PAs_read_f: [read_f]int) : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_pset: Map_6774_6775, 
      Civl_mem: [int]StampedValue, 
      Civl_pset: Map_6774_6775 :: 
    IsSendFirst(s)
       && sps == AllMemIndexPieces(s)
       && 
      true
       && Civl_PAs_read_f
         == MapAdd_21874(MapConst_3_21885(0), 
          MapIte_21892_3((lambda pa: read_f :: Set_Contains_8465(sps, pa->perm->val)), 
            MapConst_3_21885(1), 
            MapConst_3_21885(0))))
}

implementation main_s(s: Fraction_5798_5799, sps: Set_6344) returns (Civl_PAs_read_s: [read_s]int)
{
  var data: [Fraction_5843_35]StampedValue;

  /*** structured program:
    assume {:add_to_pool "MemIndices", 0, NumMemIndices} {:add_to_pool "Data", data} true;
    call {:linear sps} create_asyncs_4718((lambda pa: read_s :: Set_Contains_8465(sps, pa->perm->val)));
  **** end structured program */

  anon0:
    Civl_PAs_read_s := MapConst_3_21981(0);
    assume {:add_to_pool "MemIndices", 0, NumMemIndices} {:add_to_pool "Data", data} true;
    Civl_PAs_read_s := MapAdd_21970(Civl_PAs_read_s, 
      MapIte_21988_3((lambda pa: read_s :: Set_Contains_8465(sps, pa->perm->val)), 
        MapConst_3_21981(1), 
        MapConst_3_21981(0)));
    return;
}



procedure {:inline 1} main_s(s: Fraction_5798_5799, sps: Set_6344) returns (Civl_PAs_read_s: [read_s]int);



function {:inline} Civl_InputOutputRelation_main_s(s: Fraction_5798_5799, sps: Set_6344, Civl_PAs_read_s: [read_s]int) : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_pset: Map_6774_6775, 
      Civl_mem: [int]StampedValue, 
      Civl_pset: Map_6774_6775 :: 
    IsSendSecond(s)
       && sps == AllMemIndexPieces(s)
       && 
      true
       && Civl_PAs_read_s
         == MapAdd_21970(MapConst_3_21981(0), 
          MapIte_21988_3((lambda pa: read_s :: Set_Contains_8465(sps, pa->perm->val)), 
            MapConst_3_21981(1), 
            MapConst_3_21981(0))))
}

implementation Civl_CommutativityChecker_ReceiveSecond_ReceiveSecond(first_one_r: One_6925, 
    first_s: Fraction_5798_5799, 
    second_one_r: One_6925, 
    second_s: Fraction_5798_5799)
   returns (first_sps: Set_6344, 
    first_snapshot: [int]StampedValue, 
    second_sps: Set_6344, 
    second_snapshot: [int]StampedValue)
{

  init:
    call first_sps, first_snapshot := ReceiveSecond(first_one_r, first_s);
    call second_sps, second_snapshot := ReceiveSecond(second_one_r, second_s);
    assert (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
          MapImp_9297(Set_Collector_6344(first_sps), 
                MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
               == MapConst_5_9297(true)
             && MapImp_9297(Map_Collector_6774_6775(pset), 
                MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
               == MapConst_5_9297(true))
         && (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
          MapImp_9297(Set_Collector_6344(first_sps), 
                MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
               == MapConst_5_9297(true)
             && MapImp_9297(Set_Collector_6344(second_sps), 
                MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
               == MapConst_5_9297(true)
             && MapImp_9297(Map_Collector_6774_6775(pset), 
                MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(2)))
               == MapConst_5_9297(true))
       ==> second_sps == Map_Extract_9619_4501(old(pset), AllMemIndexPieces(second_s))->dom
         && second_snapshot
           == (lambda second_x: int :: 
            Map_Extract_9619_4501(old(pset), AllMemIndexPieces(second_s))->val[Fraction_5843_35(second_s, second_x, MemIndices())])
         && pset
           == Map_Exclude_9619_4501(Map_Exclude_9619_4501(old(pset), AllMemIndexPieces(second_s)), 
            AllMemIndexPieces(first_s))
         && first_sps
           == Map_Extract_9619_4501(Map_Exclude_9619_4501(old(pset), AllMemIndexPieces(second_s)), 
              AllMemIndexPieces(first_s))->dom
         && first_snapshot
           == (lambda first_x: int :: 
            Map_Extract_9619_4501(Map_Exclude_9619_4501(old(pset), AllMemIndexPieces(second_s)), 
                AllMemIndexPieces(first_s))->val[Fraction_5843_35(first_s, first_x, MemIndices())]);
    return;
}



procedure Civl_CommutativityChecker_ReceiveSecond_ReceiveSecond(first_one_r: One_6925, 
    first_s: Fraction_5798_5799, 
    second_one_r: One_6925, 
    second_s: Fraction_5798_5799)
   returns (first_sps: Set_6344, 
    first_snapshot: [int]StampedValue, 
    second_sps: Set_6344, 
    second_snapshot: [int]StampedValue);
  requires true;
  requires (exists Civl_partition_Fraction_5798_5799: [Fraction_5798_5799]int :: 
    MapImp_6897(One_Collector_6925(first_one_r), 
          MapEq_6897_3(Civl_partition_Fraction_5798_5799, MapConst_3_6897(0)))
         == MapConst_5_6897(true)
       && MapImp_6897(One_Collector_6925(second_one_r), 
          MapEq_6897_3(Civl_partition_Fraction_5798_5799, MapConst_3_6897(1)))
         == MapConst_5_6897(true));
  requires Map_WellFormed_6774_6775(pset);
  requires first_one_r->val->val == first_s->val;
  requires IsReceive(first_one_r->val);
  requires IsSendSecond(first_s);
  requires Set_IsSubset_9297(AllMemIndexPieces(first_s), pset->dom);
  requires second_one_r->val->val == second_s->val;
  requires IsReceive(second_one_r->val);
  requires IsSendSecond(second_s);
  requires Set_IsSubset_9297(AllMemIndexPieces(second_s), pset->dom);
  modifies mem, pset;



implementation Civl_GatePreservationChecker_ReceiveSecond_ReceiveSecond(first_one_r: One_6925, 
    first_s: Fraction_5798_5799, 
    second_one_r: One_6925, 
    second_s: Fraction_5798_5799)
   returns (first_sps: Set_6344, 
    first_snapshot: [int]StampedValue, 
    second_sps: Set_6344, 
    second_snapshot: [int]StampedValue)
{

  init:
    call second_sps, second_snapshot := ReceiveSecond(second_one_r, second_s);
    assert (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
        MapImp_9297(Set_Collector_6344(second_sps), 
              MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
             == MapConst_5_9297(true)
           && MapImp_9297(Map_Collector_6774_6775(pset), 
              MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
             == MapConst_5_9297(true))
       ==> first_one_r->val->val == first_s->val;
    assert (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
        MapImp_9297(Set_Collector_6344(second_sps), 
              MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
             == MapConst_5_9297(true)
           && MapImp_9297(Map_Collector_6774_6775(pset), 
              MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
             == MapConst_5_9297(true))
       ==> IsReceive(first_one_r->val);
    assert (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
        MapImp_9297(Set_Collector_6344(second_sps), 
              MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
             == MapConst_5_9297(true)
           && MapImp_9297(Map_Collector_6774_6775(pset), 
              MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
             == MapConst_5_9297(true))
       ==> IsSendSecond(first_s);
    assert (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
        MapImp_9297(Set_Collector_6344(second_sps), 
              MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
             == MapConst_5_9297(true)
           && MapImp_9297(Map_Collector_6774_6775(pset), 
              MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
             == MapConst_5_9297(true))
       ==> Set_IsSubset_9297(AllMemIndexPieces(first_s), pset->dom);
    return;
}



procedure Civl_GatePreservationChecker_ReceiveSecond_ReceiveSecond(first_one_r: One_6925, 
    first_s: Fraction_5798_5799, 
    second_one_r: One_6925, 
    second_s: Fraction_5798_5799)
   returns (first_sps: Set_6344, 
    first_snapshot: [int]StampedValue, 
    second_sps: Set_6344, 
    second_snapshot: [int]StampedValue);
  requires true;
  requires (exists Civl_partition_Fraction_5798_5799: [Fraction_5798_5799]int :: 
    MapImp_6897(One_Collector_6925(first_one_r), 
          MapEq_6897_3(Civl_partition_Fraction_5798_5799, MapConst_3_6897(0)))
         == MapConst_5_6897(true)
       && MapImp_6897(One_Collector_6925(second_one_r), 
          MapEq_6897_3(Civl_partition_Fraction_5798_5799, MapConst_3_6897(1)))
         == MapConst_5_6897(true));
  requires Map_WellFormed_6774_6775(pset);
  requires first_one_r->val->val == first_s->val;
  requires IsReceive(first_one_r->val);
  requires IsSendSecond(first_s);
  requires Set_IsSubset_9297(AllMemIndexPieces(first_s), pset->dom);
  requires second_one_r->val->val == second_s->val;
  requires IsReceive(second_one_r->val);
  requires IsSendSecond(second_s);
  requires Set_IsSubset_9297(AllMemIndexPieces(second_s), pset->dom);
  modifies mem, pset;



implementation Civl_FailurePreservationChecker_ReceiveSecond_ReceiveSecond(first_one_r: One_6925, 
    first_s: Fraction_5798_5799, 
    second_one_r: One_6925, 
    second_s: Fraction_5798_5799)
   returns (first_sps: Set_6344, 
    first_snapshot: [int]StampedValue, 
    second_sps: Set_6344, 
    second_snapshot: [int]StampedValue)
{

  init:
    call second_sps, second_snapshot := ReceiveSecond(second_one_r, second_s);
    assert (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
        MapImp_9297(Set_Collector_6344(second_sps), 
              MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
             == MapConst_5_9297(true)
           && MapImp_9297(Map_Collector_6774_6775(pset), 
              MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
             == MapConst_5_9297(true))
       ==> !(
        first_one_r->val->val == first_s->val
         && IsReceive(first_one_r->val)
         && IsSendSecond(first_s)
         && Set_IsSubset_9297(AllMemIndexPieces(first_s), pset->dom));
    return;
}



procedure Civl_FailurePreservationChecker_ReceiveSecond_ReceiveSecond(first_one_r: One_6925, 
    first_s: Fraction_5798_5799, 
    second_one_r: One_6925, 
    second_s: Fraction_5798_5799)
   returns (first_sps: Set_6344, 
    first_snapshot: [int]StampedValue, 
    second_sps: Set_6344, 
    second_snapshot: [int]StampedValue);
  requires true;
  requires (exists Civl_partition_Fraction_5798_5799: [Fraction_5798_5799]int :: 
    MapImp_6897(One_Collector_6925(first_one_r), 
          MapEq_6897_3(Civl_partition_Fraction_5798_5799, MapConst_3_6897(0)))
         == MapConst_5_6897(true)
       && MapImp_6897(One_Collector_6925(second_one_r), 
          MapEq_6897_3(Civl_partition_Fraction_5798_5799, MapConst_3_6897(1)))
         == MapConst_5_6897(true));
  requires Map_WellFormed_6774_6775(pset);
  requires !(
    first_one_r->val->val == first_s->val
     && IsReceive(first_one_r->val)
     && IsSendSecond(first_s)
     && Set_IsSubset_9297(AllMemIndexPieces(first_s), pset->dom));
  requires second_one_r->val->val == second_s->val;
  requires IsReceive(second_one_r->val);
  requires IsSendSecond(second_s);
  requires Set_IsSubset_9297(AllMemIndexPieces(second_s), pset->dom);
  modifies mem, pset;



implementation Civl_CommutativityChecker_ReceiveFirst_ReceiveSecond(first_one_r: One_6925, 
    first_s: Fraction_5798_5799, 
    second_one_r: One_6925, 
    second_s: Fraction_5798_5799)
   returns (first_sps: Set_6344, 
    first_snapshot: [int]StampedValue, 
    second_sps: Set_6344, 
    second_snapshot: [int]StampedValue)
{

  init:
    call first_sps, first_snapshot := ReceiveFirst(first_one_r, first_s);
    call second_sps, second_snapshot := ReceiveSecond(second_one_r, second_s);
    assert (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
          MapImp_9297(Set_Collector_6344(first_sps), 
                MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
               == MapConst_5_9297(true)
             && MapImp_9297(Map_Collector_6774_6775(pset), 
                MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
               == MapConst_5_9297(true))
         && (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
          MapImp_9297(Set_Collector_6344(first_sps), 
                MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
               == MapConst_5_9297(true)
             && MapImp_9297(Set_Collector_6344(second_sps), 
                MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
               == MapConst_5_9297(true)
             && MapImp_9297(Map_Collector_6774_6775(pset), 
                MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(2)))
               == MapConst_5_9297(true))
       ==> Set_IsSubset_9297(AllMemIndexPieces(first_s), 
          Map_Exclude_9619_4501(old(pset), AllMemIndexPieces(second_s))->dom)
         && second_sps == Map_Extract_9619_4501(old(pset), AllMemIndexPieces(second_s))->dom
         && second_snapshot
           == (lambda second_x: int :: 
            Map_Extract_9619_4501(old(pset), AllMemIndexPieces(second_s))->val[Fraction_5843_35(second_s, second_x, MemIndices())])
         && pset
           == Map_Exclude_9619_4501(Map_Exclude_9619_4501(old(pset), AllMemIndexPieces(second_s)), 
            AllMemIndexPieces(first_s))
         && first_sps
           == Map_Extract_9619_4501(Map_Exclude_9619_4501(old(pset), AllMemIndexPieces(second_s)), 
              AllMemIndexPieces(first_s))->dom
         && first_snapshot
           == (lambda first_x: int :: 
            Map_Extract_9619_4501(Map_Exclude_9619_4501(old(pset), AllMemIndexPieces(second_s)), 
                AllMemIndexPieces(first_s))->val[Fraction_5843_35(first_s, first_x, MemIndices())]);
    return;
}



procedure Civl_CommutativityChecker_ReceiveFirst_ReceiveSecond(first_one_r: One_6925, 
    first_s: Fraction_5798_5799, 
    second_one_r: One_6925, 
    second_s: Fraction_5798_5799)
   returns (first_sps: Set_6344, 
    first_snapshot: [int]StampedValue, 
    second_sps: Set_6344, 
    second_snapshot: [int]StampedValue);
  requires true;
  requires (exists Civl_partition_Fraction_5798_5799: [Fraction_5798_5799]int :: 
    MapImp_6897(One_Collector_6925(first_one_r), 
          MapEq_6897_3(Civl_partition_Fraction_5798_5799, MapConst_3_6897(0)))
         == MapConst_5_6897(true)
       && MapImp_6897(One_Collector_6925(second_one_r), 
          MapEq_6897_3(Civl_partition_Fraction_5798_5799, MapConst_3_6897(1)))
         == MapConst_5_6897(true));
  requires Map_WellFormed_6774_6775(pset);
  requires first_one_r->val->val == first_s->val;
  requires IsReceive(first_one_r->val);
  requires IsSendFirst(first_s) || IsSendSecond(first_s);
  requires second_one_r->val->val == second_s->val;
  requires IsReceive(second_one_r->val);
  requires IsSendSecond(second_s);
  requires Set_IsSubset_9297(AllMemIndexPieces(second_s), pset->dom);
  modifies mem, pset;



implementation Civl_GatePreservationChecker_ReceiveSecond_ReceiveFirst(first_one_r: One_6925, 
    first_s: Fraction_5798_5799, 
    second_one_r: One_6925, 
    second_s: Fraction_5798_5799)
   returns (first_sps: Set_6344, 
    first_snapshot: [int]StampedValue, 
    second_sps: Set_6344, 
    second_snapshot: [int]StampedValue)
{

  init:
    call second_sps, second_snapshot := ReceiveFirst(second_one_r, second_s);
    assert (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
        MapImp_9297(Set_Collector_6344(second_sps), 
              MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
             == MapConst_5_9297(true)
           && MapImp_9297(Map_Collector_6774_6775(pset), 
              MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
             == MapConst_5_9297(true))
       ==> first_one_r->val->val == first_s->val;
    assert (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
        MapImp_9297(Set_Collector_6344(second_sps), 
              MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
             == MapConst_5_9297(true)
           && MapImp_9297(Map_Collector_6774_6775(pset), 
              MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
             == MapConst_5_9297(true))
       ==> IsReceive(first_one_r->val);
    assert (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
        MapImp_9297(Set_Collector_6344(second_sps), 
              MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
             == MapConst_5_9297(true)
           && MapImp_9297(Map_Collector_6774_6775(pset), 
              MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
             == MapConst_5_9297(true))
       ==> IsSendSecond(first_s);
    assert (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
        MapImp_9297(Set_Collector_6344(second_sps), 
              MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
             == MapConst_5_9297(true)
           && MapImp_9297(Map_Collector_6774_6775(pset), 
              MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
             == MapConst_5_9297(true))
       ==> Set_IsSubset_9297(AllMemIndexPieces(first_s), pset->dom);
    return;
}



procedure Civl_GatePreservationChecker_ReceiveSecond_ReceiveFirst(first_one_r: One_6925, 
    first_s: Fraction_5798_5799, 
    second_one_r: One_6925, 
    second_s: Fraction_5798_5799)
   returns (first_sps: Set_6344, 
    first_snapshot: [int]StampedValue, 
    second_sps: Set_6344, 
    second_snapshot: [int]StampedValue);
  requires true;
  requires (exists Civl_partition_Fraction_5798_5799: [Fraction_5798_5799]int :: 
    MapImp_6897(One_Collector_6925(first_one_r), 
          MapEq_6897_3(Civl_partition_Fraction_5798_5799, MapConst_3_6897(0)))
         == MapConst_5_6897(true)
       && MapImp_6897(One_Collector_6925(second_one_r), 
          MapEq_6897_3(Civl_partition_Fraction_5798_5799, MapConst_3_6897(1)))
         == MapConst_5_6897(true));
  requires Map_WellFormed_6774_6775(pset);
  requires first_one_r->val->val == first_s->val;
  requires IsReceive(first_one_r->val);
  requires IsSendSecond(first_s);
  requires Set_IsSubset_9297(AllMemIndexPieces(first_s), pset->dom);
  requires second_one_r->val->val == second_s->val;
  requires IsReceive(second_one_r->val);
  requires IsSendFirst(second_s) || IsSendSecond(second_s);
  modifies mem, pset;



implementation Civl_CommutativityChecker_ReceiveFirst_ReceiveFirst(first_one_r: One_6925, 
    first_s: Fraction_5798_5799, 
    second_one_r: One_6925, 
    second_s: Fraction_5798_5799)
   returns (first_sps: Set_6344, 
    first_snapshot: [int]StampedValue, 
    second_sps: Set_6344, 
    second_snapshot: [int]StampedValue)
{

  init:
    call first_sps, first_snapshot := ReceiveFirst(first_one_r, first_s);
    call second_sps, second_snapshot := ReceiveFirst(second_one_r, second_s);
    assert (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
          MapImp_9297(Set_Collector_6344(first_sps), 
                MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
               == MapConst_5_9297(true)
             && MapImp_9297(Map_Collector_6774_6775(pset), 
                MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
               == MapConst_5_9297(true))
         && (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
          MapImp_9297(Set_Collector_6344(first_sps), 
                MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
               == MapConst_5_9297(true)
             && MapImp_9297(Set_Collector_6344(second_sps), 
                MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
               == MapConst_5_9297(true)
             && MapImp_9297(Map_Collector_6774_6775(pset), 
                MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(2)))
               == MapConst_5_9297(true))
       ==> Set_IsSubset_9297(AllMemIndexPieces(second_s), old(pset)->dom)
         && Set_IsSubset_9297(AllMemIndexPieces(first_s), 
          Map_Exclude_9619_4501(old(pset), AllMemIndexPieces(second_s))->dom)
         && second_sps == Map_Extract_9619_4501(old(pset), AllMemIndexPieces(second_s))->dom
         && second_snapshot
           == (lambda second_x: int :: 
            Map_Extract_9619_4501(old(pset), AllMemIndexPieces(second_s))->val[Fraction_5843_35(second_s, second_x, MemIndices())])
         && pset
           == Map_Exclude_9619_4501(Map_Exclude_9619_4501(old(pset), AllMemIndexPieces(second_s)), 
            AllMemIndexPieces(first_s))
         && first_sps
           == Map_Extract_9619_4501(Map_Exclude_9619_4501(old(pset), AllMemIndexPieces(second_s)), 
              AllMemIndexPieces(first_s))->dom
         && first_snapshot
           == (lambda first_x: int :: 
            Map_Extract_9619_4501(Map_Exclude_9619_4501(old(pset), AllMemIndexPieces(second_s)), 
                AllMemIndexPieces(first_s))->val[Fraction_5843_35(first_s, first_x, MemIndices())]);
    return;
}



procedure Civl_CommutativityChecker_ReceiveFirst_ReceiveFirst(first_one_r: One_6925, 
    first_s: Fraction_5798_5799, 
    second_one_r: One_6925, 
    second_s: Fraction_5798_5799)
   returns (first_sps: Set_6344, 
    first_snapshot: [int]StampedValue, 
    second_sps: Set_6344, 
    second_snapshot: [int]StampedValue);
  requires true;
  requires (exists Civl_partition_Fraction_5798_5799: [Fraction_5798_5799]int :: 
    MapImp_6897(One_Collector_6925(first_one_r), 
          MapEq_6897_3(Civl_partition_Fraction_5798_5799, MapConst_3_6897(0)))
         == MapConst_5_6897(true)
       && MapImp_6897(One_Collector_6925(second_one_r), 
          MapEq_6897_3(Civl_partition_Fraction_5798_5799, MapConst_3_6897(1)))
         == MapConst_5_6897(true));
  requires Map_WellFormed_6774_6775(pset);
  requires first_one_r->val->val == first_s->val;
  requires IsReceive(first_one_r->val);
  requires IsSendFirst(first_s) || IsSendSecond(first_s);
  requires second_one_r->val->val == second_s->val;
  requires IsReceive(second_one_r->val);
  requires IsSendFirst(second_s) || IsSendSecond(second_s);
  modifies mem, pset;



implementation Civl_CommutativityChecker_ReceiveFirst_main_f'(first_one_r: One_6925, 
    first_s: Fraction_5798_5799, 
    second_s: Fraction_5798_5799, 
    second_sps: Set_6344)
   returns (first_sps: Set_6344, first_snapshot: [int]StampedValue)
{

  init:
    call first_sps, first_snapshot := ReceiveFirst(first_one_r, first_s);
    call main_f'(second_s, second_sps);
    assert (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
          MapImp_9297(Set_Collector_6344(first_sps), 
                MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
               == MapConst_5_9297(true)
             && MapImp_9297(Map_Collector_6774_6775(pset), 
                MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
               == MapConst_5_9297(true))
         && (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
          MapImp_9297(Set_Collector_6344(first_sps), 
                MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
               == MapConst_5_9297(true)
             && MapImp_9297(Map_Collector_6774_6775(pset), 
                MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
               == MapConst_5_9297(true))
       ==> (exists {:pool "Data"} Civl_second_data#0: [Fraction_5843_35]StampedValue :: 
        { Trigger_main_f'_data(Civl_second_data#0) } 
        true
           && (forall second_i: int :: 
            1 <= second_i && second_i <= NumMemIndices
               ==> (var x := MemIndexPiece(second_s, second_i); 
                Civl_second_data#0[x]->ts < mem[second_i]->ts
                   || Civl_second_data#0[x] == mem[second_i]))
           && Set_IsSubset_9297(AllMemIndexPieces(first_s), 
            Map_Union_11673_4501(old(pset), 
                Map_6774_6775(second_sps, 
                  MapIte_11504_4635(second_sps->val, Civl_second_data#0, MapConst_4635_11504(Default_4635()))))->dom)
           && pset
             == Map_Exclude_9619_4501(Map_Union_11673_4501(old(pset), 
                Map_6774_6775(second_sps, 
                  MapIte_11504_4635(second_sps->val, Civl_second_data#0, MapConst_4635_11504(Default_4635())))), 
              AllMemIndexPieces(first_s))
           && first_sps
             == Map_Extract_9619_4501(Map_Union_11673_4501(old(pset), 
                  Map_6774_6775(second_sps, 
                    MapIte_11504_4635(second_sps->val, Civl_second_data#0, MapConst_4635_11504(Default_4635())))), 
                AllMemIndexPieces(first_s))->dom
           && first_snapshot
             == (lambda first_x: int :: 
              Map_Extract_9619_4501(Map_Union_11673_4501(old(pset), 
                    Map_6774_6775(second_sps, 
                      MapIte_11504_4635(second_sps->val, Civl_second_data#0, MapConst_4635_11504(Default_4635())))), 
                  AllMemIndexPieces(first_s))->val[Fraction_5843_35(first_s, first_x, MemIndices())])
           && mem == old(mem));
    return;
}



procedure Civl_CommutativityChecker_ReceiveFirst_main_f'(first_one_r: One_6925, 
    first_s: Fraction_5798_5799, 
    second_s: Fraction_5798_5799, 
    second_sps: Set_6344)
   returns (first_sps: Set_6344, first_snapshot: [int]StampedValue);
  requires true;
  requires (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
    MapImp_9297(Set_Collector_6344(second_sps), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
         == MapConst_5_9297(true)
       && MapImp_9297(Map_Collector_6774_6775(pset), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
         == MapConst_5_9297(true));
  requires Map_WellFormed_6774_6775(pset);
  requires first_one_r->val->val == first_s->val;
  requires IsReceive(first_one_r->val);
  requires IsSendFirst(first_s) || IsSendSecond(first_s);
  requires IsSendFirst(second_s);
  requires second_sps == AllMemIndexPieces(second_s);
  modifies mem, pset;



implementation Civl_CommutativityChecker_ReceiveFirst_read_f(first_one_r: One_6925, first_s: Fraction_5798_5799, second_perm: One_12014)
   returns (first_sps: Set_6344, first_snapshot: [int]StampedValue)
{

  init:
    call first_sps, first_snapshot := ReceiveFirst(first_one_r, first_s);
    call read_f(second_perm);
    assert (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
          MapImp_9297(Set_Collector_6344(first_sps), 
                MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
               == MapConst_5_9297(true)
             && MapImp_9297(Map_Collector_6774_6775(pset), 
                MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
               == MapConst_5_9297(true))
         && (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
          MapImp_9297(Set_Collector_6344(first_sps), 
                MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
               == MapConst_5_9297(true)
             && MapImp_9297(Map_Collector_6774_6775(pset), 
                MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
               == MapConst_5_9297(true))
       ==> (exists {:pool "SV_read_f"} Civl_second_sv#0: StampedValue :: 
        { Trigger_read_f_sv(Civl_second_sv#0) } 
        true
           && true
           && (Civl_second_sv#0->ts < mem[second_perm->val->id]->ts
             || Civl_second_sv#0 == mem[second_perm->val->id])
           && true
           && Set_IsSubset_9297(AllMemIndexPieces(first_s), 
            Map_Update_13105_4501(old(pset), 
                Cell_12762_12763(second_perm->val, Civl_second_sv#0)->key, 
                Cell_12762_12763(second_perm->val, Civl_second_sv#0)->val)->dom)
           && pset
             == Map_Exclude_9619_4501(Map_Update_13105_4501(old(pset), 
                Cell_12762_12763(second_perm->val, Civl_second_sv#0)->key, 
                Cell_12762_12763(second_perm->val, Civl_second_sv#0)->val), 
              AllMemIndexPieces(first_s))
           && first_sps
             == Map_Extract_9619_4501(Map_Update_13105_4501(old(pset), 
                  Cell_12762_12763(second_perm->val, Civl_second_sv#0)->key, 
                  Cell_12762_12763(second_perm->val, Civl_second_sv#0)->val), 
                AllMemIndexPieces(first_s))->dom
           && first_snapshot
             == (lambda first_x: int :: 
              Map_Extract_9619_4501(Map_Update_13105_4501(old(pset), 
                    Cell_12762_12763(second_perm->val, Civl_second_sv#0)->key, 
                    Cell_12762_12763(second_perm->val, Civl_second_sv#0)->val), 
                  AllMemIndexPieces(first_s))->val[Fraction_5843_35(first_s, first_x, MemIndices())])
           && mem == old(mem));
    return;
}



procedure Civl_CommutativityChecker_ReceiveFirst_read_f(first_one_r: One_6925, first_s: Fraction_5798_5799, second_perm: One_12014)
   returns (first_sps: Set_6344, first_snapshot: [int]StampedValue);
  requires true;
  requires (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
    MapImp_9297(One_Collector_12014(second_perm), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
         == MapConst_5_9297(true)
       && MapImp_9297(Map_Collector_6774_6775(pset), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
         == MapConst_5_9297(true));
  requires Map_WellFormed_6774_6775(pset);
  requires first_one_r->val->val == first_s->val;
  requires IsReceive(first_one_r->val);
  requires IsSendFirst(first_s) || IsSendSecond(first_s);
  requires IsSendFirst(second_perm->val->val) && IsValidMemIndexPiece(second_perm->val);
  modifies mem, pset;



implementation Civl_CommutativityChecker_ReceiveFirst_main_s'(first_one_r: One_6925, 
    first_s: Fraction_5798_5799, 
    second_s: Fraction_5798_5799, 
    second_sps: Set_6344)
   returns (first_sps: Set_6344, first_snapshot: [int]StampedValue)
{

  init:
    call first_sps, first_snapshot := ReceiveFirst(first_one_r, first_s);
    call main_s'(second_s, second_sps);
    assert (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
          MapImp_9297(Set_Collector_6344(first_sps), 
                MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
               == MapConst_5_9297(true)
             && MapImp_9297(Map_Collector_6774_6775(pset), 
                MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
               == MapConst_5_9297(true))
         && (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
          MapImp_9297(Set_Collector_6344(first_sps), 
                MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
               == MapConst_5_9297(true)
             && MapImp_9297(Map_Collector_6774_6775(pset), 
                MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
               == MapConst_5_9297(true))
       ==> (exists {:pool "Data"} Civl_second_data#0: [Fraction_5843_35]StampedValue :: 
        { Trigger_main_s'_data(Civl_second_data#0) } 
        true
           && (forall second_i: int :: 
            1 <= second_i && second_i <= NumMemIndices
               ==> (var x := MemIndexPiece(second_s, second_i); 
                Civl_second_data#0[x]->ts > mem[second_i]->ts
                   || Civl_second_data#0[x] == mem[second_i]))
           && Set_IsSubset_9297(AllMemIndexPieces(first_s), 
            Map_Union_11673_4501(old(pset), 
                Map_6774_6775(second_sps, 
                  MapIte_11504_4635(second_sps->val, Civl_second_data#0, MapConst_4635_11504(Default_4635()))))->dom)
           && pset
             == Map_Exclude_9619_4501(Map_Union_11673_4501(old(pset), 
                Map_6774_6775(second_sps, 
                  MapIte_11504_4635(second_sps->val, Civl_second_data#0, MapConst_4635_11504(Default_4635())))), 
              AllMemIndexPieces(first_s))
           && first_sps
             == Map_Extract_9619_4501(Map_Union_11673_4501(old(pset), 
                  Map_6774_6775(second_sps, 
                    MapIte_11504_4635(second_sps->val, Civl_second_data#0, MapConst_4635_11504(Default_4635())))), 
                AllMemIndexPieces(first_s))->dom
           && first_snapshot
             == (lambda first_x: int :: 
              Map_Extract_9619_4501(Map_Union_11673_4501(old(pset), 
                    Map_6774_6775(second_sps, 
                      MapIte_11504_4635(second_sps->val, Civl_second_data#0, MapConst_4635_11504(Default_4635())))), 
                  AllMemIndexPieces(first_s))->val[Fraction_5843_35(first_s, first_x, MemIndices())])
           && mem == old(mem));
    return;
}



procedure Civl_CommutativityChecker_ReceiveFirst_main_s'(first_one_r: One_6925, 
    first_s: Fraction_5798_5799, 
    second_s: Fraction_5798_5799, 
    second_sps: Set_6344)
   returns (first_sps: Set_6344, first_snapshot: [int]StampedValue);
  requires true;
  requires (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
    MapImp_9297(Set_Collector_6344(second_sps), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
         == MapConst_5_9297(true)
       && MapImp_9297(Map_Collector_6774_6775(pset), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
         == MapConst_5_9297(true));
  requires Map_WellFormed_6774_6775(pset);
  requires first_one_r->val->val == first_s->val;
  requires IsReceive(first_one_r->val);
  requires IsSendFirst(first_s) || IsSendSecond(first_s);
  requires IsSendSecond(second_s);
  requires second_sps == AllMemIndexPieces(second_s);
  modifies mem, pset;



implementation Civl_CommutativityChecker_ReceiveFirst_read_s(first_one_r: One_6925, first_s: Fraction_5798_5799, second_perm: One_12014)
   returns (first_sps: Set_6344, first_snapshot: [int]StampedValue)
{

  init:
    call first_sps, first_snapshot := ReceiveFirst(first_one_r, first_s);
    call read_s(second_perm);
    assert (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
          MapImp_9297(Set_Collector_6344(first_sps), 
                MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
               == MapConst_5_9297(true)
             && MapImp_9297(Map_Collector_6774_6775(pset), 
                MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
               == MapConst_5_9297(true))
         && (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
          MapImp_9297(Set_Collector_6344(first_sps), 
                MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
               == MapConst_5_9297(true)
             && MapImp_9297(Map_Collector_6774_6775(pset), 
                MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
               == MapConst_5_9297(true))
       ==> (exists {:pool "SV_read_s"} Civl_second_sv#0: StampedValue :: 
        { Trigger_read_s_sv(Civl_second_sv#0) } 
        true
           && true
           && (Civl_second_sv#0->ts > mem[second_perm->val->id]->ts
             || Civl_second_sv#0 == mem[second_perm->val->id])
           && true
           && Set_IsSubset_9297(AllMemIndexPieces(first_s), 
            Map_Update_13105_4501(old(pset), 
                Cell_12762_12763(second_perm->val, Civl_second_sv#0)->key, 
                Cell_12762_12763(second_perm->val, Civl_second_sv#0)->val)->dom)
           && pset
             == Map_Exclude_9619_4501(Map_Update_13105_4501(old(pset), 
                Cell_12762_12763(second_perm->val, Civl_second_sv#0)->key, 
                Cell_12762_12763(second_perm->val, Civl_second_sv#0)->val), 
              AllMemIndexPieces(first_s))
           && first_sps
             == Map_Extract_9619_4501(Map_Update_13105_4501(old(pset), 
                  Cell_12762_12763(second_perm->val, Civl_second_sv#0)->key, 
                  Cell_12762_12763(second_perm->val, Civl_second_sv#0)->val), 
                AllMemIndexPieces(first_s))->dom
           && first_snapshot
             == (lambda first_x: int :: 
              Map_Extract_9619_4501(Map_Update_13105_4501(old(pset), 
                    Cell_12762_12763(second_perm->val, Civl_second_sv#0)->key, 
                    Cell_12762_12763(second_perm->val, Civl_second_sv#0)->val), 
                  AllMemIndexPieces(first_s))->val[Fraction_5843_35(first_s, first_x, MemIndices())])
           && mem == old(mem));
    return;
}



procedure Civl_CommutativityChecker_ReceiveFirst_read_s(first_one_r: One_6925, first_s: Fraction_5798_5799, second_perm: One_12014)
   returns (first_sps: Set_6344, first_snapshot: [int]StampedValue);
  requires true;
  requires (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
    MapImp_9297(One_Collector_12014(second_perm), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
         == MapConst_5_9297(true)
       && MapImp_9297(Map_Collector_6774_6775(pset), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
         == MapConst_5_9297(true));
  requires Map_WellFormed_6774_6775(pset);
  requires first_one_r->val->val == first_s->val;
  requires IsReceive(first_one_r->val);
  requires IsSendFirst(first_s) || IsSendSecond(first_s);
  requires IsSendSecond(second_perm->val->val) && IsValidMemIndexPiece(second_perm->val);
  modifies mem, pset;



implementation Civl_CommutativityChecker_write_read_s(first_i: int, first_v: Value, second_perm: One_12014)
{

  init:
    call write(first_i, first_v);
    call read_s(second_perm);
    assert true
       ==> (exists {:pool "SV_read_s"} Civl_second_sv#0: StampedValue :: 
        { Trigger_read_s_sv(Civl_second_sv#0) } 
        true
           && true
           && (Civl_second_sv#0->ts > old(mem)[second_perm->val->id]->ts
             || Civl_second_sv#0 == old(mem)[second_perm->val->id])
           && true
           && pset
             == Map_Update_13105_4501(old(pset), 
              Cell_12762_12763(second_perm->val, Civl_second_sv#0)->key, 
              Cell_12762_12763(second_perm->val, Civl_second_sv#0)->val)
           && mem == old(mem)[first_i := StampedValue(old(mem)[first_i]->ts + 1, first_v)]);
    return;
}



procedure Civl_CommutativityChecker_write_read_s(first_i: int, first_v: Value, second_perm: One_12014);
  requires true;
  requires (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
    MapImp_9297(One_Collector_12014(second_perm), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
         == MapConst_5_9297(true)
       && MapImp_9297(Map_Collector_6774_6775(pset), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
         == MapConst_5_9297(true));
  requires Map_WellFormed_6774_6775(pset);
  requires IsSendSecond(second_perm->val->val) && IsValidMemIndexPiece(second_perm->val);
  modifies mem, pset;



implementation Civl_CommutativityChecker_main_f'_ReceiveSecond(first_s: Fraction_5798_5799, 
    first_sps: Set_6344, 
    second_one_r: One_6925, 
    second_s: Fraction_5798_5799)
   returns (second_sps: Set_6344, second_snapshot: [int]StampedValue)
{

  init:
    call main_f'(first_s, first_sps);
    call second_sps, second_snapshot := ReceiveSecond(second_one_r, second_s);
    assert (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
        MapImp_9297(Set_Collector_6344(second_sps), 
              MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
             == MapConst_5_9297(true)
           && MapImp_9297(Map_Collector_6774_6775(pset), 
              MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
             == MapConst_5_9297(true))
       ==> (exists {:pool "Data"} Civl_first_data#0: [Fraction_5843_35]StampedValue :: 
        { Trigger_main_f'_data(Civl_first_data#0) } 
        true
           && (forall first_i: int :: 
            1 <= first_i && first_i <= NumMemIndices
               ==> (var x := MemIndexPiece(first_s, first_i); 
                Civl_first_data#0[x]->ts < mem[first_i]->ts
                   || Civl_first_data#0[x] == mem[first_i]))
           && second_sps == Map_Extract_9619_4501(old(pset), AllMemIndexPieces(second_s))->dom
           && second_snapshot
             == (lambda second_x: int :: 
              Map_Extract_9619_4501(old(pset), AllMemIndexPieces(second_s))->val[Fraction_5843_35(second_s, second_x, MemIndices())])
           && pset
             == Map_Union_11673_4501(Map_Exclude_9619_4501(old(pset), AllMemIndexPieces(second_s)), 
              Map_6774_6775(first_sps, 
                MapIte_11504_4635(first_sps->val, Civl_first_data#0, MapConst_4635_11504(Default_4635()))))
           && mem == old(mem));
    return;
}



procedure Civl_CommutativityChecker_main_f'_ReceiveSecond(first_s: Fraction_5798_5799, 
    first_sps: Set_6344, 
    second_one_r: One_6925, 
    second_s: Fraction_5798_5799)
   returns (second_sps: Set_6344, second_snapshot: [int]StampedValue);
  requires true;
  requires (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
    MapImp_9297(Set_Collector_6344(first_sps), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
         == MapConst_5_9297(true)
       && MapImp_9297(Map_Collector_6774_6775(pset), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
         == MapConst_5_9297(true));
  requires Map_WellFormed_6774_6775(pset);
  requires IsSendFirst(first_s);
  requires first_sps == AllMemIndexPieces(first_s);
  requires second_one_r->val->val == second_s->val;
  requires IsReceive(second_one_r->val);
  requires IsSendSecond(second_s);
  requires Set_IsSubset_9297(AllMemIndexPieces(second_s), pset->dom);
  modifies mem, pset;



implementation Civl_GatePreservationChecker_ReceiveSecond_main_f'(first_one_r: One_6925, 
    first_s: Fraction_5798_5799, 
    second_s: Fraction_5798_5799, 
    second_sps: Set_6344)
   returns (first_sps: Set_6344, first_snapshot: [int]StampedValue)
{

  init:
    call main_f'(second_s, second_sps);
    assert true ==> first_one_r->val->val == first_s->val;
    assert true ==> IsReceive(first_one_r->val);
    assert true ==> IsSendSecond(first_s);
    assert true ==> Set_IsSubset_9297(AllMemIndexPieces(first_s), pset->dom);
    return;
}



procedure Civl_GatePreservationChecker_ReceiveSecond_main_f'(first_one_r: One_6925, 
    first_s: Fraction_5798_5799, 
    second_s: Fraction_5798_5799, 
    second_sps: Set_6344)
   returns (first_sps: Set_6344, first_snapshot: [int]StampedValue);
  requires true;
  requires (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
    MapImp_9297(Set_Collector_6344(second_sps), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
         == MapConst_5_9297(true)
       && MapImp_9297(Map_Collector_6774_6775(pset), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
         == MapConst_5_9297(true));
  requires Map_WellFormed_6774_6775(pset);
  requires first_one_r->val->val == first_s->val;
  requires IsReceive(first_one_r->val);
  requires IsSendSecond(first_s);
  requires Set_IsSubset_9297(AllMemIndexPieces(first_s), pset->dom);
  requires IsSendFirst(second_s);
  requires second_sps == AllMemIndexPieces(second_s);
  modifies mem, pset;



implementation Civl_CommutativityChecker_read_f_read_s(first_perm: One_12014, second_perm: One_12014)
{

  init:
    call read_f(first_perm);
    call read_s(second_perm);
    assert true
       ==> (exists {:pool "SV_read_s"} Civl_second_sv#0: StampedValue, 
          {:pool "SV_read_f"} Civl_first_sv#0: StampedValue :: 
        { Trigger_read_s_sv(Civl_second_sv#0), Trigger_read_f_sv(Civl_first_sv#0) } 
        true
           && true
           && (Civl_second_sv#0->ts > mem[second_perm->val->id]->ts
             || Civl_second_sv#0 == mem[second_perm->val->id])
           && true
           && true
           && true
           && (Civl_first_sv#0->ts < mem[first_perm->val->id]->ts
             || Civl_first_sv#0 == mem[first_perm->val->id])
           && true
           && pset
             == Map_Update_13105_4501(Map_Update_13105_4501(old(pset), 
                Cell_12762_12763(second_perm->val, Civl_second_sv#0)->key, 
                Cell_12762_12763(second_perm->val, Civl_second_sv#0)->val), 
              Cell_12762_12763(first_perm->val, Civl_first_sv#0)->key, 
              Cell_12762_12763(first_perm->val, Civl_first_sv#0)->val)
           && mem == old(mem));
    return;
}



procedure Civl_CommutativityChecker_read_f_read_s(first_perm: One_12014, second_perm: One_12014);
  requires true;
  requires (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
    MapImp_9297(One_Collector_12014(first_perm), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
         == MapConst_5_9297(true)
       && MapImp_9297(One_Collector_12014(second_perm), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
         == MapConst_5_9297(true)
       && MapImp_9297(Map_Collector_6774_6775(pset), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(2)))
         == MapConst_5_9297(true));
  requires Map_WellFormed_6774_6775(pset);
  requires IsSendFirst(first_perm->val->val) && IsValidMemIndexPiece(first_perm->val);
  requires IsSendSecond(second_perm->val->val) && IsValidMemIndexPiece(second_perm->val);
  modifies mem, pset;



implementation Civl_CommutativityChecker_main_s'_ReceiveSecond(first_s: Fraction_5798_5799, 
    first_sps: Set_6344, 
    second_one_r: One_6925, 
    second_s: Fraction_5798_5799)
   returns (second_sps: Set_6344, second_snapshot: [int]StampedValue)
{

  init:
    call main_s'(first_s, first_sps);
    call second_sps, second_snapshot := ReceiveSecond(second_one_r, second_s);
    assert (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
        MapImp_9297(Set_Collector_6344(second_sps), 
              MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
             == MapConst_5_9297(true)
           && MapImp_9297(Map_Collector_6774_6775(pset), 
              MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
             == MapConst_5_9297(true))
       ==> (exists {:pool "Data"} Civl_first_data#0: [Fraction_5843_35]StampedValue :: 
        { Trigger_main_s'_data(Civl_first_data#0) } 
        true
           && (forall first_i: int :: 
            1 <= first_i && first_i <= NumMemIndices
               ==> (var x := MemIndexPiece(first_s, first_i); 
                Civl_first_data#0[x]->ts > mem[first_i]->ts
                   || Civl_first_data#0[x] == mem[first_i]))
           && second_sps == Map_Extract_9619_4501(old(pset), AllMemIndexPieces(second_s))->dom
           && second_snapshot
             == (lambda second_x: int :: 
              Map_Extract_9619_4501(old(pset), AllMemIndexPieces(second_s))->val[Fraction_5843_35(second_s, second_x, MemIndices())])
           && pset
             == Map_Union_11673_4501(Map_Exclude_9619_4501(old(pset), AllMemIndexPieces(second_s)), 
              Map_6774_6775(first_sps, 
                MapIte_11504_4635(first_sps->val, Civl_first_data#0, MapConst_4635_11504(Default_4635()))))
           && mem == old(mem));
    return;
}



procedure Civl_CommutativityChecker_main_s'_ReceiveSecond(first_s: Fraction_5798_5799, 
    first_sps: Set_6344, 
    second_one_r: One_6925, 
    second_s: Fraction_5798_5799)
   returns (second_sps: Set_6344, second_snapshot: [int]StampedValue);
  requires true;
  requires (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
    MapImp_9297(Set_Collector_6344(first_sps), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
         == MapConst_5_9297(true)
       && MapImp_9297(Map_Collector_6774_6775(pset), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
         == MapConst_5_9297(true));
  requires Map_WellFormed_6774_6775(pset);
  requires IsSendSecond(first_s);
  requires first_sps == AllMemIndexPieces(first_s);
  requires second_one_r->val->val == second_s->val;
  requires IsReceive(second_one_r->val);
  requires IsSendSecond(second_s);
  requires Set_IsSubset_9297(AllMemIndexPieces(second_s), pset->dom);
  modifies mem, pset;



implementation Civl_GatePreservationChecker_ReceiveSecond_main_s'(first_one_r: One_6925, 
    first_s: Fraction_5798_5799, 
    second_s: Fraction_5798_5799, 
    second_sps: Set_6344)
   returns (first_sps: Set_6344, first_snapshot: [int]StampedValue)
{

  init:
    call main_s'(second_s, second_sps);
    assert true ==> first_one_r->val->val == first_s->val;
    assert true ==> IsReceive(first_one_r->val);
    assert true ==> IsSendSecond(first_s);
    assert true ==> Set_IsSubset_9297(AllMemIndexPieces(first_s), pset->dom);
    return;
}



procedure Civl_GatePreservationChecker_ReceiveSecond_main_s'(first_one_r: One_6925, 
    first_s: Fraction_5798_5799, 
    second_s: Fraction_5798_5799, 
    second_sps: Set_6344)
   returns (first_sps: Set_6344, first_snapshot: [int]StampedValue);
  requires true;
  requires (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
    MapImp_9297(Set_Collector_6344(second_sps), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
         == MapConst_5_9297(true)
       && MapImp_9297(Map_Collector_6774_6775(pset), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
         == MapConst_5_9297(true));
  requires Map_WellFormed_6774_6775(pset);
  requires first_one_r->val->val == first_s->val;
  requires IsReceive(first_one_r->val);
  requires IsSendSecond(first_s);
  requires Set_IsSubset_9297(AllMemIndexPieces(first_s), pset->dom);
  requires IsSendSecond(second_s);
  requires second_sps == AllMemIndexPieces(second_s);
  modifies mem, pset;



implementation Civl_CommutativityChecker_read_s_read_s(first_perm: One_12014, second_perm: One_12014)
{

  init:
    call read_s(first_perm);
    call read_s(second_perm);
    assert true
       ==> (exists {:pool "SV_read_s"} Civl_second_sv#0: StampedValue, 
          {:pool "SV_read_s"} Civl_first_sv#0: StampedValue :: 
        { Trigger_read_s_sv(Civl_second_sv#0), Trigger_read_s_sv(Civl_first_sv#0) } 
        true
           && true
           && (Civl_second_sv#0->ts > mem[second_perm->val->id]->ts
             || Civl_second_sv#0 == mem[second_perm->val->id])
           && true
           && true
           && true
           && (Civl_first_sv#0->ts > mem[first_perm->val->id]->ts
             || Civl_first_sv#0 == mem[first_perm->val->id])
           && true
           && pset
             == Map_Update_13105_4501(Map_Update_13105_4501(old(pset), 
                Cell_12762_12763(second_perm->val, Civl_second_sv#0)->key, 
                Cell_12762_12763(second_perm->val, Civl_second_sv#0)->val), 
              Cell_12762_12763(first_perm->val, Civl_first_sv#0)->key, 
              Cell_12762_12763(first_perm->val, Civl_first_sv#0)->val)
           && mem == old(mem));
    return;
}



procedure Civl_CommutativityChecker_read_s_read_s(first_perm: One_12014, second_perm: One_12014);
  requires true;
  requires (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
    MapImp_9297(One_Collector_12014(first_perm), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
         == MapConst_5_9297(true)
       && MapImp_9297(One_Collector_12014(second_perm), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
         == MapConst_5_9297(true)
       && MapImp_9297(Map_Collector_6774_6775(pset), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(2)))
         == MapConst_5_9297(true));
  requires Map_WellFormed_6774_6775(pset);
  requires IsSendSecond(first_perm->val->val) && IsValidMemIndexPiece(first_perm->val);
  requires IsSendSecond(second_perm->val->val) && IsValidMemIndexPiece(second_perm->val);
  modifies mem, pset;



implementation Civl_CooperationChecker_read_s(perm: One_12014)
{

  init:
    assert (exists {:pool "SV_read_s"} Civl_sv#0: StampedValue :: 
      true
         && true
         && (Civl_sv#0->ts > old(mem)[perm->val->id]->ts
           || Civl_sv#0 == old(mem)[perm->val->id])
         && true);
    return;
}



procedure Civl_CooperationChecker_read_s(perm: One_12014);
  requires true;
  requires (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
    MapImp_9297(One_Collector_12014(perm), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
         == MapConst_5_9297(true)
       && MapImp_9297(Map_Collector_6774_6775(pset), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
         == MapConst_5_9297(true));
  requires Map_WellFormed_6774_6775(pset);
  requires {:add_to_pool "SV_read_s", mem[perm->val->id]} IsSendSecond(perm->val->val) && IsValidMemIndexPiece(perm->val);
  modifies mem, pset;



implementation Civl_CommutativityChecker_read_f_ReceiveFirst_1(first_perm: One_12014, second_one_r: One_6925, second_s: Fraction_5798_5799)
   returns (second_sps: Set_6344, second_snapshot: [int]StampedValue)
{

  init:
    call read_f(first_perm);
    call second_sps, second_snapshot := ReceiveFirst(second_one_r, second_s);
    assert (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
        MapImp_9297(Set_Collector_6344(second_sps), 
              MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
             == MapConst_5_9297(true)
           && MapImp_9297(Map_Collector_6774_6775(pset), 
              MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
             == MapConst_5_9297(true))
       ==> (exists {:pool "SV_read_f"} Civl_first_sv#0: StampedValue :: 
        { Trigger_read_f_sv(Civl_first_sv#0) } 
        Set_IsSubset_9297(AllMemIndexPieces(second_s), old(pset)->dom)
           && true
           && true
           && (Civl_first_sv#0->ts < mem[first_perm->val->id]->ts
             || Civl_first_sv#0 == mem[first_perm->val->id])
           && true
           && second_sps == Map_Extract_9619_4501(old(pset), AllMemIndexPieces(second_s))->dom
           && second_snapshot
             == (lambda second_x: int :: 
              Map_Extract_9619_4501(old(pset), AllMemIndexPieces(second_s))->val[Fraction_5843_35(second_s, second_x, MemIndices())])
           && pset
             == Map_Update_13105_4501(Map_Exclude_9619_4501(old(pset), AllMemIndexPieces(second_s)), 
              Cell_12762_12763(first_perm->val, Civl_first_sv#0)->key, 
              Cell_12762_12763(first_perm->val, Civl_first_sv#0)->val)
           && mem == old(mem));
    return;
}



procedure Civl_CommutativityChecker_read_f_ReceiveFirst_1(first_perm: One_12014, second_one_r: One_6925, second_s: Fraction_5798_5799)
   returns (second_sps: Set_6344, second_snapshot: [int]StampedValue);
  requires true;
  requires (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
    MapImp_9297(One_Collector_12014(first_perm), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
         == MapConst_5_9297(true)
       && MapImp_9297(Map_Collector_6774_6775(pset), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
         == MapConst_5_9297(true));
  requires Map_WellFormed_6774_6775(pset);
  requires IsSendFirst(first_perm->val->val) && IsValidMemIndexPiece(first_perm->val);
  requires second_one_r->val->val == second_s->val;
  requires IsReceive(second_one_r->val);
  requires IsSendFirst(second_s) || IsSendSecond(second_s);
  requires !Set_IsSubset_9297(AllMemIndexPieces(first_perm->val->val), 
    Set_Add_12677(pset->dom, first_perm->val));
  modifies mem, pset;



implementation Civl_CommutativityChecker_read_f_write_1(first_perm: One_12014, second_i: int, second_v: Value)
{

  init:
    call read_f(first_perm);
    call write(second_i, second_v);
    assert true
       ==> (exists {:pool "SV_read_f"} Civl_first_sv#0: StampedValue :: 
        { Trigger_read_f_sv(Civl_first_sv#0) } 
        true
           && true
           && (Civl_first_sv#0->ts < mem[first_perm->val->id]->ts
             || Civl_first_sv#0 == mem[first_perm->val->id])
           && true
           && mem == old(mem)[second_i := StampedValue(old(mem)[second_i]->ts + 1, second_v)]
           && pset
             == Map_Update_13105_4501(old(pset), 
              Cell_12762_12763(first_perm->val, Civl_first_sv#0)->key, 
              Cell_12762_12763(first_perm->val, Civl_first_sv#0)->val));
    return;
}



procedure Civl_CommutativityChecker_read_f_write_1(first_perm: One_12014, second_i: int, second_v: Value);
  requires true;
  requires (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
    MapImp_9297(One_Collector_12014(first_perm), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
         == MapConst_5_9297(true)
       && MapImp_9297(Map_Collector_6774_6775(pset), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
         == MapConst_5_9297(true));
  requires Map_WellFormed_6774_6775(pset);
  requires IsSendFirst(first_perm->val->val) && IsValidMemIndexPiece(first_perm->val);
  requires !Set_IsSubset_9297(AllMemIndexPieces(first_perm->val->val), 
    Set_Add_12677(pset->dom, first_perm->val));
  modifies mem, pset;



implementation Civl_CommutativityChecker_read_f_read_f_1(first_perm: One_12014, second_perm: One_12014)
{

  init:
    call read_f(first_perm);
    call read_f(second_perm);
    assert true
       ==> (exists {:pool "SV_read_f"} Civl_second_sv#0: StampedValue, 
          {:pool "SV_read_f"} Civl_first_sv#0: StampedValue :: 
        { Trigger_read_f_sv(Civl_second_sv#0), Trigger_read_f_sv(Civl_first_sv#0) } 
        true
           && true
           && (Civl_second_sv#0->ts < mem[second_perm->val->id]->ts
             || Civl_second_sv#0 == mem[second_perm->val->id])
           && true
           && true
           && true
           && (Civl_first_sv#0->ts < mem[first_perm->val->id]->ts
             || Civl_first_sv#0 == mem[first_perm->val->id])
           && true
           && pset
             == Map_Update_13105_4501(Map_Update_13105_4501(old(pset), 
                Cell_12762_12763(second_perm->val, Civl_second_sv#0)->key, 
                Cell_12762_12763(second_perm->val, Civl_second_sv#0)->val), 
              Cell_12762_12763(first_perm->val, Civl_first_sv#0)->key, 
              Cell_12762_12763(first_perm->val, Civl_first_sv#0)->val)
           && mem == old(mem));
    return;
}



procedure Civl_CommutativityChecker_read_f_read_f_1(first_perm: One_12014, second_perm: One_12014);
  requires true;
  requires (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
    MapImp_9297(One_Collector_12014(first_perm), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
         == MapConst_5_9297(true)
       && MapImp_9297(One_Collector_12014(second_perm), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
         == MapConst_5_9297(true)
       && MapImp_9297(Map_Collector_6774_6775(pset), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(2)))
         == MapConst_5_9297(true));
  requires Map_WellFormed_6774_6775(pset);
  requires IsSendFirst(first_perm->val->val) && IsValidMemIndexPiece(first_perm->val);
  requires IsSendFirst(second_perm->val->val) && IsValidMemIndexPiece(second_perm->val);
  requires !Set_IsSubset_9297(AllMemIndexPieces(first_perm->val->val), 
    Set_Add_12677(pset->dom, first_perm->val));
  modifies mem, pset;



procedure Civl_Coordinator_1(one_loc_channel: One_6798) returns (snapshot: [int]StampedValue);
  modifies mem, pset;



procedure Civl__ReceiveSecond_1(one_r: One_6925, s: Fraction_5798_5799)
   returns (sps: Set_6344, snapshot: [int]StampedValue);
  modifies mem, pset;



implementation Civl_Coordinator_1(one_loc_channel: One_6798) returns (snapshot: [int]StampedValue)
{
  var channelOps: Set_6897;
  var one_r: One_6925;
  var one_s_first: One_6925;
  var one_s_second: One_6925;
  var sps_first: Set_6344;
  var sps_second: Set_6344;
  var snapshot': [int]StampedValue;
  var Civl_returnedPAs_read_s: [read_s]int;
  var Civl_global_old_mem: [int]StampedValue;
  var Civl_global_old_pset: Map_6774_6775;
  var Civl_linear_ChannelOp_available: [ChannelOp]bool;
  var Civl_linear_Fraction_5843_35_available: [Fraction_5843_35]bool;
  var Civl_linear_int_available: [int]bool;
  var Civl_linear_Loc_5796_available: [Loc_5796]bool;
  var Civl_linear_Fraction_5798_5799_available: [Fraction_5798_5799]bool;

  /*** structured program:
    call channelOps := One_To_Fractions_7062_4474(one_loc_channel, ChannelOps());
    call one_r := One_Get_7285(channelOps, ToReceive(one_loc_channel->val));
    call one_s_first := One_Get_7285(channelOps, ToSendFirst(one_loc_channel->val));
    call one_s_second := One_Get_7285(channelOps, ToSendSecond(one_loc_channel->val));
    call sps_first := One_To_Fractions_7484_249(one_s_first, MemIndices());
    call sps_second := One_To_Fractions_7484_249(one_s_second, MemIndices());
    while (true)
      invariant {:yields} true;
      invariant sps_first == AllMemIndexPieces(one_s_first->val);
      invariant sps_second == AllMemIndexPieces(one_s_second->val);
    {
        async call {:skip} _main_f(one_s_first->val, sps_first);
        par Yield() | YieldFirstScan(one_r, one_s_first->val);
        call sps_first, snapshot := _ReceiveFirst(one_r, one_s_first->val);
        call _main_s(one_s_second->val, sps_second);
        call sps_second, snapshot' := _ReceiveSecond(one_r, one_s_second->val);
        if (snapshot == snapshot')
        {
            return;
        }
    }
  **** end structured program */

  Civl_init:
    havoc mem, pset;
    assume Map_WellFormed_6774_6775(pset);
    Civl_global_old_mem, Civl_global_old_pset := mem, pset;
    Civl_linear_ChannelOp_available, Civl_linear_Fraction_5843_35_available, Civl_linear_int_available, Civl_linear_Loc_5796_available, Civl_linear_Fraction_5798_5799_available := MapConst_5_4434(false), MapOr_6344(Map_Collector_6774_6775(pset), MapConst_5_9297(false)), MapConst_5_2432(false), MapOr_6798(One_Collector_6798(one_loc_channel), MapConst_5_6798(false)), MapConst_5_6897(false);
    goto anon0;

  anon0:
    call channelOps := One_To_Fractions_7062_4474(one_loc_channel, ChannelOps());
    assert Set_Contains_7285(channelOps, ToReceive(one_loc_channel->val));
    channelOps := Set_Remove_7285(channelOps, ToReceive(one_loc_channel->val));
    one_r := One_6925(ToReceive(one_loc_channel->val));
    assert Set_Contains_7285(channelOps, ToSendFirst(one_loc_channel->val));
    channelOps := Set_Remove_7285(channelOps, ToSendFirst(one_loc_channel->val));
    one_s_first := One_6925(ToSendFirst(one_loc_channel->val));
    assert Set_Contains_7285(channelOps, ToSendSecond(one_loc_channel->val));
    channelOps := Set_Remove_7285(channelOps, ToSendSecond(one_loc_channel->val));
    one_s_second := One_6925(ToSendSecond(one_loc_channel->val));
    call sps_first := One_To_Fractions_7484_249(one_s_first, MemIndices());
    call sps_second := One_To_Fractions_7484_249(one_s_second, MemIndices());
    goto anon3_LoopHead, Civl_NoninterferenceChecker, Civl_RefinementChecker;

  anon3_LoopHead:
    assume (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
      MapImp_9297(Set_Collector_6344(sps_first), 
            MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
           == MapConst_5_9297(true)
         && MapImp_9297(Set_Collector_6344(sps_second), 
            MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
           == MapConst_5_9297(true)
         && MapImp_9297(Map_Collector_6774_6775(pset), 
            MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(2)))
           == MapConst_5_9297(true));
    assume (exists Civl_partition_Fraction_5798_5799: [Fraction_5798_5799]int :: 
      MapImp_6897(Set_Collector_6897(channelOps), 
            MapEq_6897_3(Civl_partition_Fraction_5798_5799, MapConst_3_6897(0)))
           == MapConst_5_6897(true)
         && MapImp_6897(One_Collector_6925(one_r), 
            MapEq_6897_3(Civl_partition_Fraction_5798_5799, MapConst_3_6897(1)))
           == MapConst_5_6897(true));
    assume Map_WellFormed_6774_6775(pset);
    assert true;
    assert true;
    mem, pset := mem, pset;
    Civl_global_old_mem, Civl_global_old_pset := mem, pset;
    Civl_linear_ChannelOp_available, Civl_linear_Fraction_5843_35_available, Civl_linear_int_available, Civl_linear_Loc_5796_available, Civl_linear_Fraction_5798_5799_available := MapConst_5_4434(false), MapOr_6344(Map_Collector_6774_6775(pset), 
      MapOr_6344(Set_Collector_6344(sps_second), 
        MapOr_6344(Set_Collector_6344(sps_first), MapConst_5_9297(false)))), MapConst_5_2432(false), MapConst_5_6798(false), MapOr_6897(One_Collector_6925(one_r), 
      MapOr_6897(Set_Collector_6897(channelOps), MapConst_5_6897(false)));
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    assume {:partition} true;
    goto anon3_LoopBody_1, Civl_NoninterferenceChecker, Civl_UnchangedChecker;

  anon3_LoopBody_1:
    call Civl_ParallelCall_Yield_1();
    Civl_global_old_mem, Civl_global_old_pset := mem, pset;
    Civl_linear_ChannelOp_available, Civl_linear_Fraction_5843_35_available, Civl_linear_int_available, Civl_linear_Loc_5796_available, Civl_linear_Fraction_5798_5799_available := MapConst_5_4434(false), MapOr_6344(Map_Collector_6774_6775(pset), 
      MapOr_6344(Set_Collector_6344(sps_second), MapConst_5_9297(false))), MapConst_5_2432(false), MapConst_5_6798(false), MapOr_6897(One_Collector_6925(one_r), 
      MapOr_6897(Set_Collector_6897(channelOps), MapConst_5_6897(false)));
    assume (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
      MapImp_9297(Set_Collector_6344(sps_second), 
            MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
           == MapConst_5_9297(true)
         && MapImp_9297(Map_Collector_6774_6775(pset), 
            MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
           == MapConst_5_9297(true));
    assume (exists Civl_partition_Fraction_5798_5799: [Fraction_5798_5799]int :: 
      MapImp_6897(Set_Collector_6897(channelOps), 
            MapEq_6897_3(Civl_partition_Fraction_5798_5799, MapConst_3_6897(0)))
           == MapConst_5_6897(true)
         && MapImp_6897(One_Collector_6925(one_r), 
            MapEq_6897_3(Civl_partition_Fraction_5798_5799, MapConst_3_6897(1)))
           == MapConst_5_6897(true));
    assume Map_WellFormed_6774_6775(pset);
    // <<< injected gate
    assume one_r->val->val == one_s_first->val->val;
    assume IsReceive(one_r->val);
    assume IsSendFirst(one_s_first->val) || IsSendSecond(one_s_first->val);
    // injected gate >>>
    call sps_first, snapshot := ReceiveFirst(one_r, one_s_first->val);
    // <<< injected gate
    assume IsSendSecond(one_s_second->val);
    assume sps_second == AllMemIndexPieces(one_s_second->val);
    // injected gate >>>
    call Civl_returnedPAs_read_s := main_s(one_s_second->val, sps_second);
    goto anon3_LoopBody_0, Civl_NoninterferenceChecker, Civl_UnchangedChecker;

  anon3_LoopBody_0:
    call sps_second, snapshot' := Civl_ParallelCall__ReceiveSecond_1(one_r, one_s_second->val);
    Civl_global_old_mem, Civl_global_old_pset := mem, pset;
    Civl_linear_ChannelOp_available, Civl_linear_Fraction_5843_35_available, Civl_linear_int_available, Civl_linear_Loc_5796_available, Civl_linear_Fraction_5798_5799_available := MapConst_5_4434(false), MapOr_6344(Map_Collector_6774_6775(pset), 
      MapOr_6344(Set_Collector_6344(sps_second), 
        MapOr_6344(Set_Collector_6344(sps_first), MapConst_5_9297(false)))), MapConst_5_2432(false), MapConst_5_6798(false), MapOr_6897(One_Collector_6925(one_r), 
      MapOr_6897(Set_Collector_6897(channelOps), MapConst_5_6897(false)));
    assume (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
      MapImp_9297(Set_Collector_6344(sps_first), 
            MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
           == MapConst_5_9297(true)
         && MapImp_9297(Set_Collector_6344(sps_second), 
            MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
           == MapConst_5_9297(true)
         && MapImp_9297(Map_Collector_6774_6775(pset), 
            MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(2)))
           == MapConst_5_9297(true));
    assume (exists Civl_partition_Fraction_5798_5799: [Fraction_5798_5799]int :: 
      MapImp_6897(Set_Collector_6897(channelOps), 
            MapEq_6897_3(Civl_partition_Fraction_5798_5799, MapConst_3_6897(0)))
           == MapConst_5_6897(true)
         && MapImp_6897(One_Collector_6925(one_r), 
            MapEq_6897_3(Civl_partition_Fraction_5798_5799, MapConst_3_6897(1)))
           == MapConst_5_6897(true));
    assume Map_WellFormed_6774_6775(pset);
    goto anon4_Then, anon4_Else;

  anon4_Else:
    assume {:partition} snapshot != snapshot';
    goto anon3_LoopHead, Civl_NoninterferenceChecker, Civl_UnchangedChecker;

  anon4_Then:
    assume {:partition} snapshot == snapshot';
    goto Civl_ReturnChecker, Civl_UnifiedReturn, Civl_NoninterferenceChecker;

  anon3_LoopDone:
    assume {:partition} !true;
    goto Civl_ReturnChecker, Civl_UnifiedReturn, Civl_NoninterferenceChecker;

  Civl_NoninterferenceChecker:
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_ChannelOp_available, Civl_linear_Fraction_5843_35_available, Civl_linear_int_available, Civl_linear_Loc_5796_available, Civl_linear_Fraction_5798_5799_available, Civl_global_old_mem, Civl_global_old_pset);
    assume false;
    return;

  Civl_RefinementChecker:
    assume false;
    return;

  Civl_UnchangedChecker:
    assume false;
    return;

  Civl_ReturnChecker:
    assume false;
    return;

  Civl_UnifiedReturn:
    return;
}



implementation Civl__ReceiveSecond_1(one_r: One_6925, s: Fraction_5798_5799)
   returns (sps: Set_6344, snapshot: [int]StampedValue)
{
  var Civl_global_old_mem: [int]StampedValue;
  var Civl_global_old_pset: Map_6774_6775;
  var Civl_pc: bool;
  var Civl_ok: bool;
  var Civl_eval: bool;
  var Civl_old_sps: Set_6344;
  var Civl_old_snapshot: [int]StampedValue;
  var Civl_linear_ChannelOp_available: [ChannelOp]bool;
  var Civl_linear_Fraction_5843_35_available: [Fraction_5843_35]bool;
  var Civl_linear_int_available: [int]bool;
  var Civl_linear_Loc_5796_available: [Loc_5796]bool;
  var Civl_linear_Fraction_5798_5799_available: [Fraction_5798_5799]bool;

  /*** structured program:
    call sps, snapshot := _ReceiveFirst(one_r, s);
  **** end structured program */

  Civl_init:
    havoc mem, pset;
    assume Map_WellFormed_6774_6775(pset);
    Civl_global_old_mem, Civl_global_old_pset := mem, pset;
    Civl_pc, Civl_ok, Civl_eval := false, false, false;
    Civl_old_sps, Civl_old_snapshot := sps, snapshot;
    assume one_r->val->val == s->val
       && IsReceive(one_r->val)
       && IsSendSecond(s)
       && Set_IsSubset_9297(AllMemIndexPieces(s), pset->dom);
    Civl_linear_ChannelOp_available, Civl_linear_Fraction_5843_35_available, Civl_linear_int_available, Civl_linear_Loc_5796_available, Civl_linear_Fraction_5798_5799_available := MapConst_5_4434(false), MapOr_6344(Map_Collector_6774_6775(pset), MapConst_5_9297(false)), MapConst_5_2432(false), MapConst_5_6798(false), MapOr_6897(One_Collector_6925(one_r), MapConst_5_6897(false));
    goto anon0;

  anon0:
    // <<< injected gate
    assert one_r->val->val == s->val;
    assert IsReceive(one_r->val);
    assert IsSendFirst(s) || IsSendSecond(s);
    // injected gate >>>
    call sps, snapshot := ReceiveFirst(one_r, s);
    goto Civl_ReturnChecker, Civl_UnifiedReturn, Civl_NoninterferenceChecker;

  Civl_NoninterferenceChecker:
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_ChannelOp_available, Civl_linear_Fraction_5843_35_available, Civl_linear_int_available, Civl_linear_Loc_5796_available, Civl_linear_Fraction_5798_5799_available, Civl_global_old_mem, Civl_global_old_pset);
    assume false;
    return;

  Civl_RefinementChecker:
    assert Civl_pc
       || 
      (mem == Civl_global_old_mem && pset == Civl_global_old_pset)
       || Civl_eval;
    assert Civl_pc
       ==> mem == Civl_global_old_mem
         && pset == Civl_global_old_pset
         && 
        sps == Civl_old_sps
         && snapshot == Civl_old_snapshot;
    assume false;
    return;

  Civl_UnchangedChecker:
    assert mem == Civl_global_old_mem && pset == Civl_global_old_pset;
    assert Civl_pc ==> sps == Civl_old_sps && snapshot == Civl_old_snapshot;
    assume false;
    return;

  Civl_ReturnChecker:
    Civl_eval := pset == Map_Exclude_9619_4501(Civl_global_old_pset, AllMemIndexPieces(s))
       && sps == Map_Extract_9619_4501(Civl_global_old_pset, AllMemIndexPieces(s))->dom
       && snapshot
         == (lambda x: int :: 
          Map_Extract_9619_4501(Civl_global_old_pset, AllMemIndexPieces(s))->val[Fraction_5843_35(s, x, MemIndices())])
       && mem == Civl_global_old_mem;
    assert Civl_pc
       || 
      (mem == Civl_global_old_mem && pset == Civl_global_old_pset)
       || Civl_eval;
    assert Civl_pc
       ==> mem == Civl_global_old_mem
         && pset == Civl_global_old_pset
         && 
        sps == Civl_old_sps
         && snapshot == Civl_old_snapshot;
    Civl_pc, Civl_ok := mem == Civl_global_old_mem && pset == Civl_global_old_pset ==> Civl_pc, Civl_eval || (sps == Civl_old_sps && snapshot == Civl_old_snapshot && Civl_ok);
    assert Civl_ok;
    assume false;
    return;

  Civl_UnifiedReturn:
    return;
}



procedure Civl_ParallelCall_Yield_1();
  modifies mem, pset;



procedure Civl_ParallelCall__ReceiveSecond_1(Civl_0_one_r: One_6925, Civl_0_s: Fraction_5798_5799)
   returns (Civl_0_sps: Set_6344, Civl_0_snapshot: [int]StampedValue);
  modifies mem, pset;



procedure Civl_PendingAsyncNoninterferenceChecker_write_1(i: int, v: Value);
  modifies mem, pset;



implementation Civl_PendingAsyncNoninterferenceChecker_write_1(i: int, v: Value)
{
  var Civl_global_old_mem: [int]StampedValue;
  var Civl_global_old_pset: Map_6774_6775;
  var Civl_linear_ChannelOp_available: [ChannelOp]bool;
  var Civl_linear_Fraction_5843_35_available: [Fraction_5843_35]bool;
  var Civl_linear_int_available: [int]bool;
  var Civl_linear_Loc_5796_available: [Loc_5796]bool;
  var Civl_linear_Fraction_5798_5799_available: [Fraction_5798_5799]bool;

  init:
    Civl_global_old_mem, Civl_global_old_pset := mem, pset;
    Civl_linear_ChannelOp_available, Civl_linear_Fraction_5843_35_available, Civl_linear_int_available, Civl_linear_Loc_5796_available, Civl_linear_Fraction_5798_5799_available := MapConst_5_4434(false), MapOr_6344(Map_Collector_6774_6775(pset), MapConst_5_9297(false)), MapConst_5_2432(false), MapConst_5_6798(false), MapConst_5_6897(false);
    call write(i, v);
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_ChannelOp_available, Civl_linear_Fraction_5843_35_available, Civl_linear_int_available, Civl_linear_Loc_5796_available, Civl_linear_Fraction_5798_5799_available, Civl_global_old_mem, Civl_global_old_pset);
    return;
}



procedure Civl_PendingAsyncNoninterferenceChecker_read_f_1(perm: One_12014);
  requires IsSendFirst(perm->val->val) && IsValidMemIndexPiece(perm->val);
  modifies mem, pset;



implementation Civl_PendingAsyncNoninterferenceChecker_read_f_1(perm: One_12014)
{
  var Civl_global_old_mem: [int]StampedValue;
  var Civl_global_old_pset: Map_6774_6775;
  var Civl_linear_ChannelOp_available: [ChannelOp]bool;
  var Civl_linear_Fraction_5843_35_available: [Fraction_5843_35]bool;
  var Civl_linear_int_available: [int]bool;
  var Civl_linear_Loc_5796_available: [Loc_5796]bool;
  var Civl_linear_Fraction_5798_5799_available: [Fraction_5798_5799]bool;

  init:
    Civl_global_old_mem, Civl_global_old_pset := mem, pset;
    Civl_linear_ChannelOp_available, Civl_linear_Fraction_5843_35_available, Civl_linear_int_available, Civl_linear_Loc_5796_available, Civl_linear_Fraction_5798_5799_available := MapConst_5_4434(false), MapOr_6344(Map_Collector_6774_6775(pset), 
      MapOr_6344(One_Collector_12014(perm), MapConst_5_9297(false))), MapConst_5_2432(false), MapConst_5_6798(false), MapConst_5_6897(false);
    call read_f(perm);
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_ChannelOp_available, Civl_linear_Fraction_5843_35_available, Civl_linear_int_available, Civl_linear_Loc_5796_available, Civl_linear_Fraction_5798_5799_available, Civl_global_old_mem, Civl_global_old_pset);
    return;
}



procedure Civl_PendingAsyncNoninterferenceChecker_read_s_1(perm: One_12014);
  requires IsSendSecond(perm->val->val) && IsValidMemIndexPiece(perm->val);
  modifies mem, pset;



implementation Civl_PendingAsyncNoninterferenceChecker_read_s_1(perm: One_12014)
{
  var Civl_global_old_mem: [int]StampedValue;
  var Civl_global_old_pset: Map_6774_6775;
  var Civl_linear_ChannelOp_available: [ChannelOp]bool;
  var Civl_linear_Fraction_5843_35_available: [Fraction_5843_35]bool;
  var Civl_linear_int_available: [int]bool;
  var Civl_linear_Loc_5796_available: [Loc_5796]bool;
  var Civl_linear_Fraction_5798_5799_available: [Fraction_5798_5799]bool;

  init:
    Civl_global_old_mem, Civl_global_old_pset := mem, pset;
    Civl_linear_ChannelOp_available, Civl_linear_Fraction_5843_35_available, Civl_linear_int_available, Civl_linear_Loc_5796_available, Civl_linear_Fraction_5798_5799_available := MapConst_5_4434(false), MapOr_6344(Map_Collector_6774_6775(pset), 
      MapOr_6344(One_Collector_12014(perm), MapConst_5_9297(false))), MapConst_5_2432(false), MapConst_5_6798(false), MapConst_5_6897(false);
    call read_s(perm);
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_ChannelOp_available, Civl_linear_Fraction_5843_35_available, Civl_linear_int_available, Civl_linear_Loc_5796_available, Civl_linear_Fraction_5798_5799_available, Civl_global_old_mem, Civl_global_old_pset);
    return;
}



procedure Civl_PendingAsyncNoninterferenceChecker_main_f_1(s: Fraction_5798_5799, sps: Set_6344) returns (Civl_PAs_read_f: [read_f]int);
  requires IsSendFirst(s);
  requires sps == AllMemIndexPieces(s);
  modifies mem, pset;



implementation Civl_PendingAsyncNoninterferenceChecker_main_f_1(s: Fraction_5798_5799, sps: Set_6344) returns (Civl_PAs_read_f: [read_f]int)
{
  var Civl_global_old_mem: [int]StampedValue;
  var Civl_global_old_pset: Map_6774_6775;
  var Civl_linear_ChannelOp_available: [ChannelOp]bool;
  var Civl_linear_Fraction_5843_35_available: [Fraction_5843_35]bool;
  var Civl_linear_int_available: [int]bool;
  var Civl_linear_Loc_5796_available: [Loc_5796]bool;
  var Civl_linear_Fraction_5798_5799_available: [Fraction_5798_5799]bool;

  init:
    Civl_global_old_mem, Civl_global_old_pset := mem, pset;
    Civl_linear_ChannelOp_available, Civl_linear_Fraction_5843_35_available, Civl_linear_int_available, Civl_linear_Loc_5796_available, Civl_linear_Fraction_5798_5799_available := MapConst_5_4434(false), MapOr_6344(Map_Collector_6774_6775(pset), 
      MapOr_6344(Set_Collector_6344(sps), MapConst_5_9297(false))), MapConst_5_2432(false), MapConst_5_6798(false), MapConst_5_6897(false);
    call Civl_PAs_read_f := main_f(s, sps);
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_ChannelOp_available, Civl_linear_Fraction_5843_35_available, Civl_linear_int_available, Civl_linear_Loc_5796_available, Civl_linear_Fraction_5798_5799_available, Civl_global_old_mem, Civl_global_old_pset);
    return;
}



procedure Civl_PendingAsyncNoninterferenceChecker_main_s_1(s: Fraction_5798_5799, sps: Set_6344) returns (Civl_PAs_read_s: [read_s]int);
  requires IsSendSecond(s);
  requires sps == AllMemIndexPieces(s);
  modifies mem, pset;



implementation Civl_PendingAsyncNoninterferenceChecker_main_s_1(s: Fraction_5798_5799, sps: Set_6344) returns (Civl_PAs_read_s: [read_s]int)
{
  var Civl_global_old_mem: [int]StampedValue;
  var Civl_global_old_pset: Map_6774_6775;
  var Civl_linear_ChannelOp_available: [ChannelOp]bool;
  var Civl_linear_Fraction_5843_35_available: [Fraction_5843_35]bool;
  var Civl_linear_int_available: [int]bool;
  var Civl_linear_Loc_5796_available: [Loc_5796]bool;
  var Civl_linear_Fraction_5798_5799_available: [Fraction_5798_5799]bool;

  init:
    Civl_global_old_mem, Civl_global_old_pset := mem, pset;
    Civl_linear_ChannelOp_available, Civl_linear_Fraction_5843_35_available, Civl_linear_int_available, Civl_linear_Loc_5796_available, Civl_linear_Fraction_5798_5799_available := MapConst_5_4434(false), MapOr_6344(Map_Collector_6774_6775(pset), 
      MapOr_6344(Set_Collector_6344(sps), MapConst_5_9297(false))), MapConst_5_2432(false), MapConst_5_6798(false), MapConst_5_6897(false);
    call Civl_PAs_read_s := main_s(s, sps);
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_ChannelOp_available, Civl_linear_Fraction_5843_35_available, Civl_linear_int_available, Civl_linear_Loc_5796_available, Civl_linear_Fraction_5798_5799_available, Civl_global_old_mem, Civl_global_old_pset);
    return;
}



procedure {:inline 1} Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_ChannelOp_in: [ChannelOp]bool, 
    Civl_linear_Fraction_5843_35_in: [Fraction_5843_35]bool, 
    Civl_linear_int_in: [int]bool, 
    Civl_linear_Loc_5796_in: [Loc_5796]bool, 
    Civl_linear_Fraction_5798_5799_in: [Fraction_5798_5799]bool, 
    Civl_global_old_mem: [int]StampedValue, 
    Civl_global_old_pset: Map_6774_6775);



implementation Civl_Wrapper_NoninterferenceChecker_1(Civl_Civl_linear_ChannelOp_in: [ChannelOp]bool, 
    Civl_Civl_linear_Fraction_5843_35_in: [Fraction_5843_35]bool, 
    Civl_Civl_linear_int_in: [int]bool, 
    Civl_Civl_linear_Loc_5796_in: [Loc_5796]bool, 
    Civl_Civl_linear_Fraction_5798_5799_in: [Fraction_5798_5799]bool, 
    Civl_Civl_global_old_mem: [int]StampedValue, 
    Civl_Civl_global_old_pset: Map_6774_6775)
{

  enter:
    return;
}



procedure Civl_Coordinator_2(one_loc_channel: One_6798) returns (snapshot: [int]StampedValue);
  modifies mem, pset;



implementation Civl_Coordinator_2(one_loc_channel: One_6798) returns (snapshot: [int]StampedValue)
{
  var channelOps: Set_6897;
  var one_r: One_6925;
  var one_s_first: One_6925;
  var one_s_second: One_6925;
  var sps_first: Set_6344;
  var sps_second: Set_6344;
  var snapshot': [int]StampedValue;
  var Civl_global_old_mem: [int]StampedValue;
  var Civl_global_old_pset: Map_6774_6775;
  var Civl_pc: bool;
  var Civl_ok: bool;
  var Civl_eval: bool;
  var Civl_old_snapshot: [int]StampedValue;
  var Civl_linear_ChannelOp_available: [ChannelOp]bool;
  var Civl_linear_Fraction_5843_35_available: [Fraction_5843_35]bool;
  var Civl_linear_int_available: [int]bool;
  var Civl_linear_Loc_5796_available: [Loc_5796]bool;
  var Civl_linear_Fraction_5798_5799_available: [Fraction_5798_5799]bool;

  /*** structured program:
    call channelOps := One_To_Fractions_7062_4474(one_loc_channel, ChannelOps());
    call one_r := One_Get_7285(channelOps, ToReceive(one_loc_channel->val));
    call one_s_first := One_Get_7285(channelOps, ToSendFirst(one_loc_channel->val));
    call one_s_second := One_Get_7285(channelOps, ToSendSecond(one_loc_channel->val));
    call sps_first := One_To_Fractions_7484_249(one_s_first, MemIndices());
    call sps_second := One_To_Fractions_7484_249(one_s_second, MemIndices());
    while (true)
      invariant {:yields} true;
      invariant sps_first == AllMemIndexPieces(one_s_first->val);
      invariant sps_second == AllMemIndexPieces(one_s_second->val);
    {
        async call {:skip} _main_f(one_s_first->val, sps_first);
        par Yield() | YieldFirstScan(one_r, one_s_first->val);
        call sps_first, snapshot := _ReceiveFirst(one_r, one_s_first->val);
        call _main_s(one_s_second->val, sps_second);
        call sps_second, snapshot' := _ReceiveSecond(one_r, one_s_second->val);
        if (snapshot == snapshot')
        {
            return;
        }
    }
  **** end structured program */

  Civl_init:
    havoc mem, pset;
    assume Map_WellFormed_6774_6775(pset);
    Civl_global_old_mem, Civl_global_old_pset := mem, pset;
    Civl_pc, Civl_ok, Civl_eval := false, false, false;
    Civl_old_snapshot := snapshot;
    assume true;
    Civl_linear_ChannelOp_available, Civl_linear_Fraction_5843_35_available, Civl_linear_int_available, Civl_linear_Loc_5796_available, Civl_linear_Fraction_5798_5799_available := MapConst_5_4434(false), MapOr_6344(Map_Collector_6774_6775(pset), MapConst_5_9297(false)), MapConst_5_2432(false), MapOr_6798(One_Collector_6798(one_loc_channel), MapConst_5_6798(false)), MapConst_5_6897(false);
    goto anon0;

  anon0:
    call channelOps := One_To_Fractions_7062_4474(one_loc_channel, ChannelOps());
    assert Set_Contains_7285(channelOps, ToReceive(one_loc_channel->val));
    channelOps := Set_Remove_7285(channelOps, ToReceive(one_loc_channel->val));
    one_r := One_6925(ToReceive(one_loc_channel->val));
    assert Set_Contains_7285(channelOps, ToSendFirst(one_loc_channel->val));
    channelOps := Set_Remove_7285(channelOps, ToSendFirst(one_loc_channel->val));
    one_s_first := One_6925(ToSendFirst(one_loc_channel->val));
    assert Set_Contains_7285(channelOps, ToSendSecond(one_loc_channel->val));
    channelOps := Set_Remove_7285(channelOps, ToSendSecond(one_loc_channel->val));
    one_s_second := One_6925(ToSendSecond(one_loc_channel->val));
    call sps_first := One_To_Fractions_7484_249(one_s_first, MemIndices());
    call sps_second := One_To_Fractions_7484_249(one_s_second, MemIndices());
    goto anon3_LoopHead, Civl_NoninterferenceChecker, Civl_RefinementChecker;

  anon3_LoopHead:
    assume (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
      MapImp_9297(Set_Collector_6344(sps_first), 
            MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
           == MapConst_5_9297(true)
         && MapImp_9297(Set_Collector_6344(sps_second), 
            MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
           == MapConst_5_9297(true)
         && MapImp_9297(Map_Collector_6774_6775(pset), 
            MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(2)))
           == MapConst_5_9297(true));
    assume (exists Civl_partition_Fraction_5798_5799: [Fraction_5798_5799]int :: 
      MapImp_6897(Set_Collector_6897(channelOps), 
            MapEq_6897_3(Civl_partition_Fraction_5798_5799, MapConst_3_6897(0)))
           == MapConst_5_6897(true)
         && MapImp_6897(One_Collector_6925(one_r), 
            MapEq_6897_3(Civl_partition_Fraction_5798_5799, MapConst_3_6897(1)))
           == MapConst_5_6897(true));
    assume Map_WellFormed_6774_6775(pset);
    assert sps_first == AllMemIndexPieces(one_s_first->val);
    assert sps_second == AllMemIndexPieces(one_s_second->val);
    assume Civl_pc || true;
    mem, pset := mem, pset;
    Civl_global_old_mem, Civl_global_old_pset := mem, pset;
    Civl_old_snapshot := snapshot;
    Civl_linear_ChannelOp_available, Civl_linear_Fraction_5843_35_available, Civl_linear_int_available, Civl_linear_Loc_5796_available, Civl_linear_Fraction_5798_5799_available := MapConst_5_4434(false), MapOr_6344(Map_Collector_6774_6775(pset), 
      MapOr_6344(Set_Collector_6344(sps_second), 
        MapOr_6344(Set_Collector_6344(sps_first), MapConst_5_9297(false)))), MapConst_5_2432(false), MapConst_5_6798(false), MapOr_6897(One_Collector_6925(one_r), 
      MapOr_6897(Set_Collector_6897(channelOps), MapConst_5_6897(false)));
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    assume {:partition} true;
    // <<< injected gate
    assert IsSendFirst(one_s_first->val);
    assert sps_first == AllMemIndexPieces(one_s_first->val);
    // injected gate >>>
    goto anon3_LoopBody_0, Civl_NoninterferenceChecker, Civl_UnchangedChecker;

  anon3_LoopBody_0:
    call Civl_ParallelCall_YieldFirstScan_2(one_r, one_s_first->val);
    assume Civl_pc || true;
    Civl_global_old_mem, Civl_global_old_pset := mem, pset;
    Civl_old_snapshot := snapshot;
    Civl_linear_ChannelOp_available, Civl_linear_Fraction_5843_35_available, Civl_linear_int_available, Civl_linear_Loc_5796_available, Civl_linear_Fraction_5798_5799_available := MapConst_5_4434(false), MapOr_6344(Map_Collector_6774_6775(pset), 
      MapOr_6344(Set_Collector_6344(sps_second), MapConst_5_9297(false))), MapConst_5_2432(false), MapConst_5_6798(false), MapOr_6897(One_Collector_6925(one_r), 
      MapOr_6897(Set_Collector_6897(channelOps), MapConst_5_6897(false)));
    assume (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
      MapImp_9297(Set_Collector_6344(sps_second), 
            MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
           == MapConst_5_9297(true)
         && MapImp_9297(Map_Collector_6774_6775(pset), 
            MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
           == MapConst_5_9297(true));
    assume (exists Civl_partition_Fraction_5798_5799: [Fraction_5798_5799]int :: 
      MapImp_6897(Set_Collector_6897(channelOps), 
            MapEq_6897_3(Civl_partition_Fraction_5798_5799, MapConst_3_6897(0)))
           == MapConst_5_6897(true)
         && MapImp_6897(One_Collector_6925(one_r), 
            MapEq_6897_3(Civl_partition_Fraction_5798_5799, MapConst_3_6897(1)))
           == MapConst_5_6897(true));
    assume Map_WellFormed_6774_6775(pset);
    // <<< injected gate
    assert one_r->val->val == one_s_first->val->val;
    assert IsReceive(one_r->val);
    assert IsSendFirst(one_s_first->val) || IsSendSecond(one_s_first->val);
    // injected gate >>>
    call sps_first, snapshot := ReceiveFirst(one_r, one_s_first->val);
    // <<< injected gate
    assert IsSendSecond(one_s_second->val);
    assert sps_second == AllMemIndexPieces(one_s_second->val);
    // injected gate >>>
    call main_s'(one_s_second->val, sps_second);
    // <<< injected gate
    assert one_r->val->val == one_s_second->val->val;
    assert IsReceive(one_r->val);
    assert IsSendSecond(one_s_second->val);
    assert Set_IsSubset_9297(AllMemIndexPieces(one_s_second->val), pset->dom);
    // injected gate >>>
    call sps_second, snapshot' := ReceiveSecond(one_r, one_s_second->val);
    goto anon4_Then, anon4_Else;

  anon4_Else:
    assume {:partition} snapshot != snapshot';
    goto anon3_LoopHead, Civl_NoninterferenceChecker, Civl_UnchangedChecker;

  anon4_Then:
    assume {:partition} snapshot == snapshot';
    goto Civl_ReturnChecker, Civl_UnifiedReturn, Civl_NoninterferenceChecker;

  anon3_LoopDone:
    assume {:partition} !true;
    goto Civl_ReturnChecker, Civl_UnifiedReturn, Civl_NoninterferenceChecker;

  Civl_NoninterferenceChecker:
    call Civl_Wrapper_NoninterferenceChecker_2(Civl_linear_ChannelOp_available, Civl_linear_Fraction_5843_35_available, Civl_linear_int_available, Civl_linear_Loc_5796_available, Civl_linear_Fraction_5798_5799_available, Civl_global_old_mem, Civl_global_old_pset);
    assume false;
    return;

  Civl_RefinementChecker:
    assert Civl_pc || mem == Civl_global_old_mem || Civl_eval;
    assert Civl_pc ==> mem == Civl_global_old_mem && snapshot == Civl_old_snapshot;
    assume false;
    return;

  Civl_UnchangedChecker:
    assert mem == Civl_global_old_mem;
    assert Civl_pc ==> snapshot == Civl_old_snapshot;
    assume false;
    return;

  Civl_ReturnChecker:
    Civl_eval := (forall i: int :: 1 <= i && i <= NumMemIndices ==> snapshot[i] == mem[i])
       && mem == Civl_global_old_mem;
    assert Civl_pc || mem == Civl_global_old_mem || Civl_eval;
    assert Civl_pc ==> mem == Civl_global_old_mem && snapshot == Civl_old_snapshot;
    Civl_pc, Civl_ok := mem == Civl_global_old_mem ==> Civl_pc, Civl_eval || (snapshot == Civl_old_snapshot && Civl_ok);
    assert Civl_ok;
    assume false;
    return;

  Civl_UnifiedReturn:
    return;
}



procedure {:inline 1} Civl_NoninterferenceChecker_yield_YieldFirstScan(Civl_linear_ChannelOp_in: [ChannelOp]bool, 
    Civl_linear_Fraction_5843_35_in: [Fraction_5843_35]bool, 
    Civl_linear_int_in: [int]bool, 
    Civl_linear_Loc_5796_in: [Loc_5796]bool, 
    Civl_linear_Fraction_5798_5799_in: [Fraction_5798_5799]bool, 
    Civl_snapshot_mem: [int]StampedValue, 
    Civl_snapshot_pset: Map_6774_6775);



implementation Civl_NoninterferenceChecker_yield_YieldFirstScan(Civl_linear_ChannelOp_in: [ChannelOp]bool, 
    Civl_linear_Fraction_5843_35_in: [Fraction_5843_35]bool, 
    Civl_linear_int_in: [int]bool, 
    Civl_linear_Loc_5796_in: [Loc_5796]bool, 
    Civl_linear_Fraction_5798_5799_in: [Fraction_5798_5799]bool, 
    Civl_snapshot_mem: [int]StampedValue, 
    Civl_snapshot_pset: Map_6774_6775)
{
  var one_r: One_6925;
  var s_first: Fraction_5798_5799;

  enter:
    goto exit, L;

  exit:
    return;

  L:
    assume (exists Civl_partition_Fraction_5798_5799: [Fraction_5798_5799]int :: 
      MapImp_6897(One_Collector_6925(one_r), 
            MapEq_6897_3(Civl_partition_Fraction_5798_5799, MapConst_3_6897(0)))
           == MapConst_5_6897(true)
         && MapImp_6897(Civl_linear_Fraction_5798_5799_in, 
            MapEq_6897_3(Civl_partition_Fraction_5798_5799, MapConst_3_6897(1)))
           == MapConst_5_6897(true));
    assume IsReceive(one_r->val);
    assume s_first == ToSendFirst(one_r->val->val);
    assume (forall piece: Fraction_5843_35 :: 
      Set_Contains_8465(AllMemIndexPieces(s_first), piece)
           && Map_Contains_8527_4501(Civl_snapshot_pset, piece)
         ==> Map_At_8596_4501(Civl_snapshot_pset, piece)->ts
             < Civl_snapshot_mem[piece->id]->ts
           || Map_At_8596_4501(Civl_snapshot_pset, piece) == Civl_snapshot_mem[piece->id]);
    assert IsReceive(one_r->val);
    assert s_first == ToSendFirst(one_r->val->val);
    assert (forall piece: Fraction_5843_35 :: 
      Set_Contains_8465(AllMemIndexPieces(s_first), piece)
           && Map_Contains_8527_4501(pset, piece)
         ==> Map_At_8596_4501(pset, piece)->ts < mem[piece->id]->ts
           || Map_At_8596_4501(pset, piece) == mem[piece->id]);
    assume false;
    return;
}



procedure Civl_ParallelCall_YieldFirstScan_2(Civl_0_one_r: One_6925, Civl_0_s_first: Fraction_5798_5799);
  requires IsReceive(Civl_0_one_r->val);
  requires Civl_0_s_first == ToSendFirst(Civl_0_one_r->val->val);
  requires (forall piece: Fraction_5843_35 :: 
    Set_Contains_8465(AllMemIndexPieces(Civl_0_s_first), piece)
         && Map_Contains_8527_4501(pset, piece)
       ==> Map_At_8596_4501(pset, piece)->ts < mem[piece->id]->ts
         || Map_At_8596_4501(pset, piece) == mem[piece->id]);
  modifies mem, pset;
  ensures IsReceive(Civl_0_one_r->val);
  ensures Civl_0_s_first == ToSendFirst(Civl_0_one_r->val->val);
  ensures (forall piece: Fraction_5843_35 :: 
    Set_Contains_8465(AllMemIndexPieces(Civl_0_s_first), piece)
         && Map_Contains_8527_4501(pset, piece)
       ==> Map_At_8596_4501(pset, piece)->ts < mem[piece->id]->ts
         || Map_At_8596_4501(pset, piece) == mem[piece->id]);



procedure Civl_PendingAsyncNoninterferenceChecker_write_2(i: int, v: Value);
  modifies mem, pset;



implementation Civl_PendingAsyncNoninterferenceChecker_write_2(i: int, v: Value)
{
  var Civl_global_old_mem: [int]StampedValue;
  var Civl_global_old_pset: Map_6774_6775;
  var Civl_linear_ChannelOp_available: [ChannelOp]bool;
  var Civl_linear_Fraction_5843_35_available: [Fraction_5843_35]bool;
  var Civl_linear_int_available: [int]bool;
  var Civl_linear_Loc_5796_available: [Loc_5796]bool;
  var Civl_linear_Fraction_5798_5799_available: [Fraction_5798_5799]bool;

  init:
    Civl_global_old_mem, Civl_global_old_pset := mem, pset;
    Civl_linear_ChannelOp_available, Civl_linear_Fraction_5843_35_available, Civl_linear_int_available, Civl_linear_Loc_5796_available, Civl_linear_Fraction_5798_5799_available := MapConst_5_4434(false), MapOr_6344(Map_Collector_6774_6775(pset), MapConst_5_9297(false)), MapConst_5_2432(false), MapConst_5_6798(false), MapConst_5_6897(false);
    call write(i, v);
    call Civl_Wrapper_NoninterferenceChecker_2(Civl_linear_ChannelOp_available, Civl_linear_Fraction_5843_35_available, Civl_linear_int_available, Civl_linear_Loc_5796_available, Civl_linear_Fraction_5798_5799_available, Civl_global_old_mem, Civl_global_old_pset);
    return;
}



procedure Civl_PendingAsyncNoninterferenceChecker_main_f'_2(s: Fraction_5798_5799, sps: Set_6344);
  requires IsSendFirst(s);
  requires sps == AllMemIndexPieces(s);
  modifies mem, pset;



implementation Civl_PendingAsyncNoninterferenceChecker_main_f'_2(s: Fraction_5798_5799, sps: Set_6344)
{
  var Civl_global_old_mem: [int]StampedValue;
  var Civl_global_old_pset: Map_6774_6775;
  var Civl_linear_ChannelOp_available: [ChannelOp]bool;
  var Civl_linear_Fraction_5843_35_available: [Fraction_5843_35]bool;
  var Civl_linear_int_available: [int]bool;
  var Civl_linear_Loc_5796_available: [Loc_5796]bool;
  var Civl_linear_Fraction_5798_5799_available: [Fraction_5798_5799]bool;

  init:
    Civl_global_old_mem, Civl_global_old_pset := mem, pset;
    Civl_linear_ChannelOp_available, Civl_linear_Fraction_5843_35_available, Civl_linear_int_available, Civl_linear_Loc_5796_available, Civl_linear_Fraction_5798_5799_available := MapConst_5_4434(false), MapOr_6344(Map_Collector_6774_6775(pset), 
      MapOr_6344(Set_Collector_6344(sps), MapConst_5_9297(false))), MapConst_5_2432(false), MapConst_5_6798(false), MapConst_5_6897(false);
    call main_f'(s, sps);
    call Civl_Wrapper_NoninterferenceChecker_2(Civl_linear_ChannelOp_available, Civl_linear_Fraction_5843_35_available, Civl_linear_int_available, Civl_linear_Loc_5796_available, Civl_linear_Fraction_5798_5799_available, Civl_global_old_mem, Civl_global_old_pset);
    return;
}



procedure Civl_PendingAsyncNoninterferenceChecker_main_s'_2(s: Fraction_5798_5799, sps: Set_6344);
  requires IsSendSecond(s);
  requires sps == AllMemIndexPieces(s);
  modifies mem, pset;



implementation Civl_PendingAsyncNoninterferenceChecker_main_s'_2(s: Fraction_5798_5799, sps: Set_6344)
{
  var Civl_global_old_mem: [int]StampedValue;
  var Civl_global_old_pset: Map_6774_6775;
  var Civl_linear_ChannelOp_available: [ChannelOp]bool;
  var Civl_linear_Fraction_5843_35_available: [Fraction_5843_35]bool;
  var Civl_linear_int_available: [int]bool;
  var Civl_linear_Loc_5796_available: [Loc_5796]bool;
  var Civl_linear_Fraction_5798_5799_available: [Fraction_5798_5799]bool;

  init:
    Civl_global_old_mem, Civl_global_old_pset := mem, pset;
    Civl_linear_ChannelOp_available, Civl_linear_Fraction_5843_35_available, Civl_linear_int_available, Civl_linear_Loc_5796_available, Civl_linear_Fraction_5798_5799_available := MapConst_5_4434(false), MapOr_6344(Map_Collector_6774_6775(pset), 
      MapOr_6344(Set_Collector_6344(sps), MapConst_5_9297(false))), MapConst_5_2432(false), MapConst_5_6798(false), MapConst_5_6897(false);
    call main_s'(s, sps);
    call Civl_Wrapper_NoninterferenceChecker_2(Civl_linear_ChannelOp_available, Civl_linear_Fraction_5843_35_available, Civl_linear_int_available, Civl_linear_Loc_5796_available, Civl_linear_Fraction_5798_5799_available, Civl_global_old_mem, Civl_global_old_pset);
    return;
}



procedure {:inline 1} Civl_Wrapper_NoninterferenceChecker_2(Civl_linear_ChannelOp_in: [ChannelOp]bool, 
    Civl_linear_Fraction_5843_35_in: [Fraction_5843_35]bool, 
    Civl_linear_int_in: [int]bool, 
    Civl_linear_Loc_5796_in: [Loc_5796]bool, 
    Civl_linear_Fraction_5798_5799_in: [Fraction_5798_5799]bool, 
    Civl_global_old_mem: [int]StampedValue, 
    Civl_global_old_pset: Map_6774_6775);



implementation Civl_Wrapper_NoninterferenceChecker_2(Civl_Civl_linear_ChannelOp_in: [ChannelOp]bool, 
    Civl_Civl_linear_Fraction_5843_35_in: [Fraction_5843_35]bool, 
    Civl_Civl_linear_int_in: [int]bool, 
    Civl_Civl_linear_Loc_5796_in: [Loc_5796]bool, 
    Civl_Civl_linear_Fraction_5798_5799_in: [Fraction_5798_5799]bool, 
    Civl_Civl_global_old_mem: [int]StampedValue, 
    Civl_Civl_global_old_pset: Map_6774_6775)
{

  enter:
    goto L_0;

  L_0:
    call Civl_NoninterferenceChecker_yield_YieldFirstScan(Civl_Civl_linear_ChannelOp_in, Civl_Civl_linear_Fraction_5843_35_in, Civl_Civl_linear_int_in, Civl_Civl_linear_Loc_5796_in, Civl_Civl_linear_Fraction_5798_5799_in, Civl_Civl_global_old_mem, Civl_Civl_global_old_pset);
    return;
}



procedure Civl_PartitionChecker_main_f(s: Fraction_5798_5799, sps: Set_6344) returns (Civl_PAs_read_f: [read_f]int);
  requires IsSendFirst(s);
  requires sps == AllMemIndexPieces(s);
  requires true;
  requires true;
  requires true;
  requires true;
  requires true;



implementation Civl_PartitionChecker_main_f(s: Fraction_5798_5799, sps: Set_6344) returns (Civl_PAs_read_f: [read_f]int)
{
  var Civl_local_Civl_PAs_read_f: read_f;

  Civl_PartitionChecker_main_f:
    call Civl_PAs_read_f := main_f(s, sps);
    assert Civl_PAs_read_f != MapConst_3_21885(0) ==> true;
    goto label_Civl_PAs_read_f;

  label_Civl_PAs_read_f:
    assume Civl_PAs_read_f[Civl_local_Civl_PAs_read_f] >= 1;
    assert IsSendFirst(Civl_local_Civl_PAs_read_f->perm->val->val)
       && IsValidMemIndexPiece(Civl_local_Civl_PAs_read_f->perm->val);
    return;
}



procedure Civl_PartitionChecker_read_f(perm: One_12014);
  requires IsSendFirst(perm->val->val) && IsValidMemIndexPiece(perm->val);
  requires true;
  requires (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
    MapImp_9297(One_Collector_12014(perm), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
         == MapConst_5_9297(true)
       && MapImp_9297(Map_Collector_6774_6775(pset), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
         == MapConst_5_9297(true));
  requires true;
  requires true;
  requires true;
  modifies pset;



implementation Civl_PartitionChecker_read_f(perm: One_12014)
{

  Civl_PartitionChecker_read_f:
    call read_f(perm);
    assert false ==> true;
    return;
}



procedure Civl_ISR_base_main_f(s: Fraction_5798_5799, sps: Set_6344) returns (Civl_PAs_read_f: [read_f]int);
  requires IsSendFirst(s);
  requires sps == AllMemIndexPieces(s);
  requires Map_WellFormed_6774_6775(pset);
  requires true;
  requires (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
    MapImp_9297(Set_Collector_6344(sps), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
         == MapConst_5_9297(true)
       && MapImp_9297(Map_Collector_6774_6775(pset), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
         == MapConst_5_9297(true));
  requires Map_WellFormed_6774_6775(pset);
  modifies pset;



implementation Civl_ISR_base_main_f(s: Fraction_5798_5799, sps: Set_6344) returns (Civl_PAs_read_f: [read_f]int)
{

  ISR_base_main_f:
    assert IsSendFirst(s);
    assert sps == AllMemIndexPieces(s);
    call Civl_PAs_read_f := main_f(s, sps);
    assert (exists {:pool "MemIndices"} Civl_j#0: int, 
          {:pool "Data"} Civl_data#0: [Fraction_5843_35]StampedValue :: 
        0 <= Civl_j#0
           && Civl_j#0 <= NumMemIndices
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0
               ==> (var x := MemIndexPiece(s, i); 
                Civl_data#0[x]->ts < mem[i]->ts || Civl_data#0[x] == mem[i]))
           && Civl_j#0 < NumMemIndices
           && true
           && pset
             == Map_Union_11673_4501(old(pset), 
              Map_6774_6775(Set_6344(MemIndexPieces(s, Civl_j#0)->val), 
                MapIte_11504_4635(Set_6344(MemIndexPieces(s, Civl_j#0)->val)->val, 
                  Civl_data#0, 
                  MapConst_4635_11504(Default_4635()))))
           && Civl_PAs_read_f
             == MapAdd_21874(MapConst_3_21885(0), 
              MapIte_21892_3((lambda {:pool "Read_PAs"} pa: read_f :: 
                  Set_Contains_8465(Set_Difference_9619(sps, Set_6344(MemIndexPieces(s, Civl_j#0)->val)), 
                    pa->perm->val)), 
                MapConst_3_21885(1), 
                MapConst_3_21885(0))))
       || (exists {:pool "MemIndices"} Civl_j#0: int, 
          {:pool "Data"} Civl_data#0: [Fraction_5843_35]StampedValue :: 
        0 <= Civl_j#0
           && Civl_j#0 <= NumMemIndices
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0
               ==> (var x := MemIndexPiece(s, i); 
                Civl_data#0[x]->ts < mem[i]->ts || Civl_data#0[x] == mem[i]))
           && NumMemIndices <= Civl_j#0
           && Civl_PAs_read_f == MapConst_3_21885(0)
           && pset
             == Map_Union_11673_4501(old(pset), 
              Map_6774_6775(Set_6344(MemIndexPieces(s, Civl_j#0)->val), 
                MapIte_11504_4635(Set_6344(MemIndexPieces(s, Civl_j#0)->val)->val, 
                  Civl_data#0, 
                  MapConst_4635_11504(Default_4635())))));
    return;
}



procedure Civl_ISR_conclusion_main_f(s: Fraction_5798_5799, sps: Set_6344) returns (Civl_PAs_read_f: [read_f]int);
  requires IsSendFirst(s);
  requires sps == AllMemIndexPieces(s);
  requires Map_WellFormed_6774_6775(pset);
  requires true;
  requires (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
    MapImp_9297(Set_Collector_6344(sps), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
         == MapConst_5_9297(true)
       && MapImp_9297(Map_Collector_6774_6775(pset), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
         == MapConst_5_9297(true));
  requires Map_WellFormed_6774_6775(pset);
  modifies pset;



implementation Civl_ISR_conclusion_main_f(s: Fraction_5798_5799, sps: Set_6344) returns (Civl_PAs_read_f: [read_f]int)
{

  ISR_conclusion_main_f:
    assert IsSendFirst(s);
    assert sps == AllMemIndexPieces(s);
    call Civl_PAs_read_f := Inv_f(s, sps);
    assume Civl_PAs_read_f == MapConst_3_21885(0);
    assert (exists {:pool "Data"} Civl_data#0: [Fraction_5843_35]StampedValue :: 
      true
         && (forall i: int :: 
          1 <= i && i <= NumMemIndices
             ==> (var x := MemIndexPiece(s, i); 
              Civl_data#0[x]->ts < mem[i]->ts || Civl_data#0[x] == mem[i]))
         && pset
           == Map_Union_11673_4501(old(pset), 
            Map_6774_6775(sps, 
              MapIte_11504_4635(sps->val, Civl_data#0, MapConst_4635_11504(Default_4635()))))
         && mem == old(mem));
    return;
}



procedure Civl_ISR_step_Inv_f_read_f(s: Fraction_5798_5799, sps: Set_6344)
   returns (Civl_PAs_read_f: [read_f]int, Civl_choice: Choice_Inv_f);
  requires IsSendFirst(s);
  requires sps == AllMemIndexPieces(s);
  requires Map_WellFormed_6774_6775(pset);
  requires true;
  requires (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
    MapImp_9297(Set_Collector_6344(sps), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
         == MapConst_5_9297(true)
       && MapImp_9297(Map_Collector_6774_6775(pset), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
         == MapConst_5_9297(true));
  requires Map_WellFormed_6774_6775(pset);
  modifies pset;



implementation Civl_ISR_step_Inv_f_read_f(s: Fraction_5798_5799, sps: Set_6344)
   returns (Civl_PAs_read_f: [read_f]int, Civl_choice: Choice_Inv_f)
{

  ISR_step_Inv_f_read_f:
    call Civl_PAs_read_f, Civl_choice := Inv_f_With_Choice(s, sps);
    assume Civl_choice is Choice_Inv_f_read_f;
    assume Civl_PAs_read_f[Civl_choice->read_f] > 0;
    Civl_PAs_read_f[Civl_choice->read_f] := Civl_PAs_read_f[Civl_choice->read_f] - 1;
    assert IsSendFirst(Civl_choice->read_f->perm->val->val)
       && IsValidMemIndexPiece(Civl_choice->read_f->perm->val);
    call read_f(Civl_choice->read_f->perm);
    assert (exists {:pool "MemIndices"} Civl_j#0: int, 
          {:pool "Data"} Civl_data#0: [Fraction_5843_35]StampedValue :: 
        0 <= Civl_j#0
           && Civl_j#0 <= NumMemIndices
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0
               ==> (var x := MemIndexPiece(s, i); 
                Civl_data#0[x]->ts < mem[i]->ts || Civl_data#0[x] == mem[i]))
           && Civl_j#0 < NumMemIndices
           && true
           && pset
             == Map_Union_11673_4501(old(pset), 
              Map_6774_6775(Set_6344(MemIndexPieces(s, Civl_j#0)->val), 
                MapIte_11504_4635(Set_6344(MemIndexPieces(s, Civl_j#0)->val)->val, 
                  Civl_data#0, 
                  MapConst_4635_11504(Default_4635()))))
           && Civl_PAs_read_f
             == MapAdd_21874(MapConst_3_21885(0), 
              MapIte_21892_3((lambda {:pool "Read_PAs"} pa: read_f :: 
                  Set_Contains_8465(Set_Difference_9619(sps, Set_6344(MemIndexPieces(s, Civl_j#0)->val)), 
                    pa->perm->val)), 
                MapConst_3_21885(1), 
                MapConst_3_21885(0))))
       || (exists {:pool "MemIndices"} Civl_j#0: int, 
          {:pool "Data"} Civl_data#0: [Fraction_5843_35]StampedValue :: 
        0 <= Civl_j#0
           && Civl_j#0 <= NumMemIndices
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0
               ==> (var x := MemIndexPiece(s, i); 
                Civl_data#0[x]->ts < mem[i]->ts || Civl_data#0[x] == mem[i]))
           && NumMemIndices <= Civl_j#0
           && Civl_PAs_read_f == MapConst_3_21885(0)
           && pset
             == Map_Union_11673_4501(old(pset), 
              Map_6774_6775(Set_6344(MemIndexPieces(s, Civl_j#0)->val), 
                MapIte_11504_4635(Set_6344(MemIndexPieces(s, Civl_j#0)->val)->val, 
                  Civl_data#0, 
                  MapConst_4635_11504(Default_4635())))));
    return;
}



procedure Civl_ISR_SideCondition_main_f(s: Fraction_5798_5799, sps: Set_6344) returns (Civl_PAs_read_f: [read_f]int);
  requires IsSendFirst(s);
  requires sps == AllMemIndexPieces(s);
  requires true;
  requires true;
  requires true;
  requires true;
  requires true;



implementation Civl_ISR_SideCondition_main_f(s: Fraction_5798_5799, sps: Set_6344) returns (Civl_PAs_read_f: [read_f]int)
{

  init:
    assume true;
    call Civl_PAs_read_f := main_f(s, sps);
    goto ChannelOp_only_put_perm_main_f, Fraction_5843_35_only_put_perm_main_f, int_only_put_perm_main_f, Loc_5796_only_put_perm_main_f, Fraction_5798_5799_only_put_perm_main_f;

  ChannelOp_only_put_perm_main_f:
    assume true;
    assert MapImp_5799(old(MapConst_5_4434(false)), MapConst_5_4434(false))
       == MapConst_5_4434(true);
    return;

  Fraction_5843_35_only_put_perm_main_f:
    assume true;
    assert MapImp_9297(old(MapConst_5_9297(false)), MapConst_5_9297(false))
       == MapConst_5_9297(true);
    return;

  int_only_put_perm_main_f:
    assume true;
    assert MapImp_35(old(MapConst_5_2432(false)), MapConst_5_2432(false))
       == MapConst_5_2432(true);
    return;

  Loc_5796_only_put_perm_main_f:
    assume true;
    assert MapImp_6798(old(MapConst_5_6798(false)), MapConst_5_6798(false))
       == MapConst_5_6798(true);
    return;

  Fraction_5798_5799_only_put_perm_main_f:
    assume true;
    assert MapImp_6897(old(MapConst_5_6897(false)), MapConst_5_6897(false))
       == MapConst_5_6897(true);
    return;
}



procedure Civl_ISR_AllPendingAsyncsInElim_read_f(perm: One_12014);
  modifies pset;



implementation Civl_ISR_AllPendingAsyncsInElim_read_f(perm: One_12014)
{

  ISR_AllPendingAsyncsInElim_read_f:
    assume !Set_IsSubset_9297(AllMemIndexPieces(perm->val->val), Set_Add_12677(pset->dom, perm->val));
    call read_f(perm);
    assert true;
    return;
}



procedure Civl_ISR_AllPendingAsyncsNotInElim_read_f(perm: One_12014);
  modifies pset;



implementation Civl_ISR_AllPendingAsyncsNotInElim_read_f(perm: One_12014)
{

  ISR_AllPendingAsyncsNotInElim_read_f:
    assume Set_IsSubset_9297(AllMemIndexPieces(perm->val->val), Set_Add_12677(pset->dom, perm->val));
    call read_f(perm);
    assert true;
    return;
}



procedure Civl_ISR_SideCondition_read_f(perm: One_12014);
  requires IsSendFirst(perm->val->val) && IsValidMemIndexPiece(perm->val);
  requires true;
  requires (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
    MapImp_9297(One_Collector_12014(perm), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
         == MapConst_5_9297(true)
       && MapImp_9297(Map_Collector_6774_6775(pset), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
         == MapConst_5_9297(true));
  requires true;
  requires true;
  requires true;
  modifies pset;



implementation Civl_ISR_SideCondition_read_f(perm: One_12014)
{

  init:
    assume !Set_IsSubset_9297(AllMemIndexPieces(perm->val->val), Set_Add_12677(pset->dom, perm->val));
    call read_f(perm);
    goto ChannelOp_only_put_perm_read_f, Fraction_5843_35_only_put_perm_read_f, int_only_put_perm_read_f, Loc_5796_only_put_perm_read_f, Fraction_5798_5799_only_put_perm_read_f;

  ChannelOp_only_put_perm_read_f:
    assume true;
    assert MapImp_5799(old(MapConst_5_4434(false)), MapConst_5_4434(false))
       == MapConst_5_4434(true);
    return;

  Fraction_5843_35_only_put_perm_read_f:
    assume true;
    assert MapImp_9297(old(MapOr_6344(Map_Collector_6774_6775(pset), MapConst_5_9297(false))), 
        MapOr_6344(Map_Collector_6774_6775(pset), MapConst_5_9297(false)))
       == MapConst_5_9297(true);
    return;

  int_only_put_perm_read_f:
    assume true;
    assert MapImp_35(old(MapConst_5_2432(false)), MapConst_5_2432(false))
       == MapConst_5_2432(true);
    return;

  Loc_5796_only_put_perm_read_f:
    assume true;
    assert MapImp_6798(old(MapConst_5_6798(false)), MapConst_5_6798(false))
       == MapConst_5_6798(true);
    return;

  Fraction_5798_5799_only_put_perm_read_f:
    assume true;
    assert MapImp_6897(old(MapConst_5_6897(false)), MapConst_5_6897(false))
       == MapConst_5_6897(true);
    return;
}



procedure Civl_ISR_InconsistencyChecker_main_f_read_f_read_f();
  modifies pset;



implementation Civl_ISR_InconsistencyChecker_main_f_read_f_read_f()
{
  var Civl_E1_read_f: read_f;
  var Civl_E2_read_f: read_f;
  var Civl_tempg_mem: [int]StampedValue;
  var Civl_tempg_pset: Map_6774_6775;
  var Civl_templ_s: Fraction_5798_5799;
  var Civl_templ_sps: Set_6344;

  ISR_InconsistencyChecker_main_f_read_f_read_f:
    assume IsSendFirst(Civl_templ_s)
       && Civl_templ_sps == AllMemIndexPieces(Civl_templ_s)
       && true;
    assume MapAnd_5799(MapConst_5_4434(false), MapConst_5_4434(false))
         == MapConst_5_4434(false)
       && MapAnd_5799(MapConst_5_4434(false), MapConst_5_4434(false))
         == MapConst_5_4434(false)
       && MapAnd_5799(MapConst_5_4434(false), MapConst_5_4434(false))
         == MapConst_5_4434(false)
       && 
      MapAnd_6344(MapOr_6344(Map_Collector_6774_6775(pset), MapConst_5_9297(false)), 
          MapOr_6344(One_Collector_12014(Civl_E1_read_f->perm), MapConst_5_9297(false)))
         == MapConst_5_9297(false)
       && MapAnd_6344(MapOr_6344(Map_Collector_6774_6775(pset), MapConst_5_9297(false)), 
          MapOr_6344(One_Collector_12014(Civl_E2_read_f->perm), MapConst_5_9297(false)))
         == MapConst_5_9297(false)
       && MapAnd_6344(MapOr_6344(One_Collector_12014(Civl_E1_read_f->perm), MapConst_5_9297(false)), 
          MapOr_6344(One_Collector_12014(Civl_E2_read_f->perm), MapConst_5_9297(false)))
         == MapConst_5_9297(false)
       && 
      MapAnd_2411(MapConst_5_2432(false), MapConst_5_2432(false))
         == MapConst_5_2432(false)
       && MapAnd_2411(MapConst_5_2432(false), MapConst_5_2432(false))
         == MapConst_5_2432(false)
       && MapAnd_2411(MapConst_5_2432(false), MapConst_5_2432(false))
         == MapConst_5_2432(false)
       && 
      MapAnd_6798(MapConst_5_6798(false), MapConst_5_6798(false))
         == MapConst_5_6798(false)
       && MapAnd_6798(MapConst_5_6798(false), MapConst_5_6798(false))
         == MapConst_5_6798(false)
       && MapAnd_6798(MapConst_5_6798(false), MapConst_5_6798(false))
         == MapConst_5_6798(false)
       && 
      MapAnd_6897(MapConst_5_6897(false), MapConst_5_6897(false))
         == MapConst_5_6897(false)
       && MapAnd_6897(MapConst_5_6897(false), MapConst_5_6897(false))
         == MapConst_5_6897(false)
       && MapAnd_6897(MapConst_5_6897(false), MapConst_5_6897(false))
         == MapConst_5_6897(false);
    assume MapImp_5799(MapConst_5_4434(false), MapConst_5_4434(false))
         == MapConst_5_4434(true)
       && MapImp_5799(MapConst_5_4434(false), MapConst_5_4434(false))
         == MapConst_5_4434(true)
       && 
      MapImp_9297(MapOr_6344(One_Collector_12014(Civl_E1_read_f->perm), MapConst_5_9297(false)), 
          MapOr_6344(Set_Collector_6344(Civl_templ_sps), MapConst_5_9297(false)))
         == MapConst_5_9297(true)
       && MapImp_9297(MapOr_6344(One_Collector_12014(Civl_E2_read_f->perm), MapConst_5_9297(false)), 
          MapOr_6344(Set_Collector_6344(Civl_templ_sps), MapConst_5_9297(false)))
         == MapConst_5_9297(true)
       && 
      MapImp_35(MapConst_5_2432(false), MapConst_5_2432(false))
         == MapConst_5_2432(true)
       && MapImp_35(MapConst_5_2432(false), MapConst_5_2432(false))
         == MapConst_5_2432(true)
       && 
      MapImp_6798(MapConst_5_6798(false), MapConst_5_6798(false))
         == MapConst_5_6798(true)
       && MapImp_6798(MapConst_5_6798(false), MapConst_5_6798(false))
         == MapConst_5_6798(true)
       && 
      MapImp_6897(MapConst_5_6897(false), MapConst_5_6897(false))
         == MapConst_5_6897(true)
       && MapImp_6897(MapConst_5_6897(false), MapConst_5_6897(false))
         == MapConst_5_6897(true);
    assert !(
      IsSendFirst(Civl_E1_read_f->perm->val->val)
       && IsValidMemIndexPiece(Civl_E1_read_f->perm->val)
       && 
      Set_IsSubset_9297(AllMemIndexPieces(Civl_E2_read_f->perm->val->val), 
        Set_Add_12677(pset->dom, Civl_E2_read_f->perm->val))
       && 
      IsSendFirst(Civl_E2_read_f->perm->val->val)
       && IsValidMemIndexPiece(Civl_E2_read_f->perm->val));
    return;
}



procedure Civl_ISL_base_main_s(s: Fraction_5798_5799, sps: Set_6344) returns (Civl_PAs_read_s: [read_s]int);
  requires IsSendSecond(s);
  requires sps == AllMemIndexPieces(s);
  requires Map_WellFormed_6774_6775(pset);
  requires true;
  requires (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
    MapImp_9297(Set_Collector_6344(sps), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
         == MapConst_5_9297(true)
       && MapImp_9297(Map_Collector_6774_6775(pset), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
         == MapConst_5_9297(true));
  requires Map_WellFormed_6774_6775(pset);
  modifies pset;



implementation Civl_ISL_base_main_s(s: Fraction_5798_5799, sps: Set_6344) returns (Civl_PAs_read_s: [read_s]int)
{

  ISL_base_main_s:
    assert IsSendSecond(s);
    assert sps == AllMemIndexPieces(s);
    call Civl_PAs_read_s := main_s(s, sps);
    assert (exists {:pool "MemIndices"} Civl_j#0: int, 
          {:pool "Data"} Civl_data#0: [Fraction_5843_35]StampedValue :: 
        0 <= Civl_j#0
           && Civl_j#0 <= NumMemIndices
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0
               ==> (var x := MemIndexPiece(s, i); 
                Civl_data#0[x]->ts > mem[i]->ts || Civl_data#0[x] == mem[i]))
           && Civl_j#0 < NumMemIndices
           && true
           && pset
             == Map_Union_11673_4501(old(pset), 
              Map_6774_6775(Set_6344(MemIndexPieces(s, Civl_j#0)->val), 
                MapIte_11504_4635(Set_6344(MemIndexPieces(s, Civl_j#0)->val)->val, 
                  Civl_data#0, 
                  MapConst_4635_11504(Default_4635()))))
           && Civl_PAs_read_s
             == MapAdd_21970(MapConst_3_21981(0), 
              MapIte_21988_3((lambda {:pool "Read_PAs"} pa: read_s :: 
                  Set_Contains_8465(Set_Difference_9619(sps, Set_6344(MemIndexPieces(s, Civl_j#0)->val)), 
                    pa->perm->val)), 
                MapConst_3_21981(1), 
                MapConst_3_21981(0))))
       || (exists {:pool "MemIndices"} Civl_j#0: int, 
          {:pool "Data"} Civl_data#0: [Fraction_5843_35]StampedValue :: 
        0 <= Civl_j#0
           && Civl_j#0 <= NumMemIndices
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0
               ==> (var x := MemIndexPiece(s, i); 
                Civl_data#0[x]->ts > mem[i]->ts || Civl_data#0[x] == mem[i]))
           && NumMemIndices <= Civl_j#0
           && Civl_PAs_read_s == MapConst_3_21981(0)
           && pset
             == Map_Union_11673_4501(old(pset), 
              Map_6774_6775(Set_6344(MemIndexPieces(s, Civl_j#0)->val), 
                MapIte_11504_4635(Set_6344(MemIndexPieces(s, Civl_j#0)->val)->val, 
                  Civl_data#0, 
                  MapConst_4635_11504(Default_4635())))));
    return;
}



procedure Civl_ISL_conclusion_main_s(s: Fraction_5798_5799, sps: Set_6344) returns (Civl_PAs_read_s: [read_s]int);
  requires IsSendSecond(s);
  requires sps == AllMemIndexPieces(s);
  requires Map_WellFormed_6774_6775(pset);
  requires true;
  requires (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
    MapImp_9297(Set_Collector_6344(sps), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
         == MapConst_5_9297(true)
       && MapImp_9297(Map_Collector_6774_6775(pset), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
         == MapConst_5_9297(true));
  requires Map_WellFormed_6774_6775(pset);
  modifies pset;



implementation Civl_ISL_conclusion_main_s(s: Fraction_5798_5799, sps: Set_6344) returns (Civl_PAs_read_s: [read_s]int)
{

  ISL_conclusion_main_s:
    assert IsSendSecond(s);
    assert sps == AllMemIndexPieces(s);
    call Civl_PAs_read_s := Inv_s(s, sps);
    assume Civl_PAs_read_s == MapConst_3_21981(0);
    assert (exists {:pool "Data"} Civl_data#0: [Fraction_5843_35]StampedValue :: 
      true
         && (forall i: int :: 
          1 <= i && i <= NumMemIndices
             ==> (var x := MemIndexPiece(s, i); 
              Civl_data#0[x]->ts > mem[i]->ts || Civl_data#0[x] == mem[i]))
         && pset
           == Map_Union_11673_4501(old(pset), 
            Map_6774_6775(sps, 
              MapIte_11504_4635(sps->val, Civl_data#0, MapConst_4635_11504(Default_4635()))))
         && mem == old(mem));
    return;
}



procedure Civl_ISL_step_Inv_s_read_s(s: Fraction_5798_5799, sps: Set_6344)
   returns (Civl_PAs_read_s: [read_s]int, Civl_choice: Choice_Inv_s);
  requires IsSendSecond(s);
  requires sps == AllMemIndexPieces(s);
  requires Map_WellFormed_6774_6775(pset);
  requires true;
  requires (exists Civl_partition_Fraction_5843_35: [Fraction_5843_35]int :: 
    MapImp_9297(Set_Collector_6344(sps), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(0)))
         == MapConst_5_9297(true)
       && MapImp_9297(Map_Collector_6774_6775(pset), 
          MapEq_6344_3(Civl_partition_Fraction_5843_35, MapConst_3_6344(1)))
         == MapConst_5_9297(true));
  requires Map_WellFormed_6774_6775(pset);
  modifies pset;



implementation Civl_ISL_step_Inv_s_read_s(s: Fraction_5798_5799, sps: Set_6344)
   returns (Civl_PAs_read_s: [read_s]int, Civl_choice: Choice_Inv_s)
{

  ISL_step_Inv_s_read_s:
    call Civl_PAs_read_s, Civl_choice := Inv_s_With_Choice(s, sps);
    assume Civl_choice is Choice_Inv_s_read_s;
    assume Civl_PAs_read_s[Civl_choice->read_s] > 0;
    Civl_PAs_read_s[Civl_choice->read_s] := Civl_PAs_read_s[Civl_choice->read_s] - 1;
    assert {:add_to_pool "SV_read_s", mem[Civl_choice->read_s->perm->val->id]} IsSendSecond(Civl_choice->read_s->perm->val->val)
       && IsValidMemIndexPiece(Civl_choice->read_s->perm->val);
    call read_s(Civl_choice->read_s->perm);
    assert (exists {:pool "MemIndices"} Civl_j#0: int, 
          {:pool "Data"} Civl_data#0: [Fraction_5843_35]StampedValue :: 
        0 <= Civl_j#0
           && Civl_j#0 <= NumMemIndices
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0
               ==> (var x := MemIndexPiece(s, i); 
                Civl_data#0[x]->ts > mem[i]->ts || Civl_data#0[x] == mem[i]))
           && Civl_j#0 < NumMemIndices
           && true
           && pset
             == Map_Union_11673_4501(old(pset), 
              Map_6774_6775(Set_6344(MemIndexPieces(s, Civl_j#0)->val), 
                MapIte_11504_4635(Set_6344(MemIndexPieces(s, Civl_j#0)->val)->val, 
                  Civl_data#0, 
                  MapConst_4635_11504(Default_4635()))))
           && Civl_PAs_read_s
             == MapAdd_21970(MapConst_3_21981(0), 
              MapIte_21988_3((lambda {:pool "Read_PAs"} pa: read_s :: 
                  Set_Contains_8465(Set_Difference_9619(sps, Set_6344(MemIndexPieces(s, Civl_j#0)->val)), 
                    pa->perm->val)), 
                MapConst_3_21981(1), 
                MapConst_3_21981(0))))
       || (exists {:pool "MemIndices"} Civl_j#0: int, 
          {:pool "Data"} Civl_data#0: [Fraction_5843_35]StampedValue :: 
        0 <= Civl_j#0
           && Civl_j#0 <= NumMemIndices
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0
               ==> (var x := MemIndexPiece(s, i); 
                Civl_data#0[x]->ts > mem[i]->ts || Civl_data#0[x] == mem[i]))
           && NumMemIndices <= Civl_j#0
           && Civl_PAs_read_s == MapConst_3_21981(0)
           && pset
             == Map_Union_11673_4501(old(pset), 
              Map_6774_6775(Set_6344(MemIndexPieces(s, Civl_j#0)->val), 
                MapIte_11504_4635(Set_6344(MemIndexPieces(s, Civl_j#0)->val)->val, 
                  Civl_data#0, 
                  MapConst_4635_11504(Default_4635())))));
    return;
}


