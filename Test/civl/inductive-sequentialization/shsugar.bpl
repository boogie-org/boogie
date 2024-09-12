// Boogie program verifier version 3.1.6.0, Copyright (c) 2003-2014, Microsoft.
// Command Line Options: snapshot-scatter-gather.bpl /civlDesugaredFile:shsugar.bpl

type Value;

type Tid;

datatype StampedValue {
  StampedValue(ts: int, value: Value)
}

datatype Permission {
  Permission(tid: Tid, mem_index: int)
}

const n: int;

var mem: [int]StampedValue;

var pSet: Set_4217;

var channels: [Tid]Option_4235;

var snapshots: [Tid][int]StampedValue;

function {:inline} WholeTidPermission(tid: Tid) : Set_4217
{
  Set_4217((lambda {:pool "D"} x: Permission :: 
      x->tid == tid && 1 <= x->mem_index && x->mem_index <= n))
}

datatype main_f {
  main_f(tid: Tid, sps: Set_4217)
}

datatype main_f' {
  main_f'(tid: Tid, sps: Set_4217)
}

datatype read_f {
  read_f(perm: One_4689)
}

const Identity: [int]int;

function {:inline} AtLeast(x: int) : [int]bool
{
  MapLe_1255(MapConst_1272_1255(x), Identity)
}

function {:inline} Range(from: int, n: int) : [int]bool
{
  MapDiff_1275(AtLeast(from), AtLeast(from + n))
}

type {:builtin "Seq"} Seq _;

pure procedure Assume(b: bool);
  ensures b;



datatype Set_4217 {
  Set_4217(val: [Permission]bool)
}

datatype Option_4235 {
  None_4235(),
  Some_4235(t: [int]StampedValue)
}

function {:inline} Set_IsSubset_3338(a: Set_4217, b: Set_4217) : bool
{
  IsSubset_3338(a->val, b->val)
}

function {:inline} IsSubset_3338(a: [Permission]bool, b: [Permission]bool) : bool
{
  MapImp_3338(a, b) == MapConst_5_3338(true)
}

function {:builtin "MapImp"} MapImp_3338([Permission]bool, [Permission]bool) : [Permission]bool;

function {:builtin "MapConst"} MapConst_5_3338(bool) : [Permission]bool;

datatype One_4689 {
  One_4689(val: Permission)
}

procedure create_asyncs_3363(PAs: [read_f]bool);



pure procedure Set_Put_3326(path: Set_4217, l: Set_4217);



function {:inline} Set_Add_3326(a: Set_4217, t: Permission) : Set_4217
{
  Set_4217(a->val[t := true])
}

pure procedure One_Put_3326(path: Set_4217, l: One_4689);



pure procedure Set_Get_3391(path: Set_4217, k: [Permission]bool) returns (l: Set_4217);



procedure set_choice_3395(choice: read_f);



function {:builtin "MapConst"} MapConst_1272_1255(int) : [int]int;

function {:builtin "MapLe"} MapLe_1255([int]int, [int]int) : [int]bool;

function {:inline} MapDiff_1275(a: [int]bool, b: [int]bool) : [int]bool
{
  MapAnd_1275(a, MapNot_1275(b))
}

function {:builtin "MapNot"} MapNot_1275([int]bool) : [int]bool;

function {:builtin "MapAnd"} MapAnd_1275([int]bool, [int]bool) : [int]bool;

datatype Vec_5 {
  Vec_5(contents: [int]bool, len: int)
}

function Default_5() : bool;

function {:builtin "MapConst"} MapConst_5_1296(bool) : [int]bool;

function {:builtin "MapIte"} MapIte_1296_5([int]bool, [int]bool, [int]bool) : [int]bool;

datatype Vec_1272 {
  Vec_1272(contents: [int]int, len: int)
}

function Default_1272() : int;

function {:builtin "MapIte"} MapIte_1296_1272([int]bool, [int]int, [int]int) : [int]int;

function {:inline} Set_Empty_4217() : Set_4217
{
  Set_4217(MapConst_5_3338(false))
}

function Set_Size_4217(a: Set_4217) : int;

function {:inline} Set_Contains_4217(a: Set_4217, t: Permission) : bool
{
  a->val[t]
}

function {:inline} Set_Remove_4217(a: Set_4217, t: Permission) : Set_4217
{
  Set_4217(a->val[t := false])
}

function {:inline} Set_Difference_4217(a: Set_4217, b: Set_4217) : Set_4217
{
  Set_4217(MapDiff_4217(a->val, b->val))
}

function {:inline} MapDiff_4217(a: [Permission]bool, b: [Permission]bool) : [Permission]bool
{
  MapAnd_4217(a, MapNot_4217(b))
}

function {:builtin "MapNot"} MapNot_4217([Permission]bool) : [Permission]bool;

function {:builtin "MapAnd"} MapAnd_4217([Permission]bool, [Permission]bool) : [Permission]bool;

function {:inline} Set_Intersection_4217(a: Set_4217, b: Set_4217) : Set_4217
{
  Set_4217(MapAnd_4217(a->val, b->val))
}

function {:inline} Set_Union_4217(a: Set_4217, b: Set_4217) : Set_4217
{
  Set_4217(MapOr_4217(a->val, b->val))
}

function {:builtin "MapOr"} MapOr_4217([Permission]bool, [Permission]bool) : [Permission]bool;

function Choice_3338(a: [Permission]bool) : Permission;

function Choice_1255(a: [int]bool) : int;

axiom n >= 1;

axiom (forall x: int :: Identity[x] == x);

axiom (forall x: Vec_1272 :: 
  { x->len } { x->contents } 
  MapIte_1296_1272(Range(0, x->len), MapConst_1272_1255(Default_1272()), x->contents)
     == MapConst_1272_1255(Default_1272()));

axiom (forall x: Vec_5 :: 
  { x->len } { x->contents } 
  MapIte_1296_5(Range(0, x->len), MapConst_5_1296(Default_5()), x->contents)
     == MapConst_5_1296(Default_5()));

axiom (forall x: Vec_1272 :: { x->len } x->len >= 0);

axiom (forall x: Vec_5 :: { x->len } x->len >= 0);

axiom (forall a: Set_4217 :: a == Set_Empty_4217() || 0 < Set_Size_4217(a));

axiom Set_Size_4217(Set_Empty_4217()) == 0;

axiom (forall a: Set_4217, t: Permission :: 
  { Set_Add_3326(a, t) } 
  Set_Size_4217(Set_Add_3326(a, t))
     == (if Set_Contains_4217(a, t) then Set_Size_4217(a) else Set_Size_4217(a) + 1));

axiom (forall a: Set_4217, t: Permission :: 
  { Set_Remove_4217(a, t) } 
  Set_Size_4217(Set_Remove_4217(a, t))
     == (if Set_Contains_4217(a, t) then Set_Size_4217(a) - 1 else Set_Size_4217(a)));

axiom (forall a: Set_4217, b: Set_4217 :: 
  { Set_Difference_4217(a, b) } 
    { Set_Intersection_4217(a, b) } 
    { Set_Union_4217(a, b) } 
  Set_Size_4217(a)
     == Set_Size_4217(Set_Difference_4217(a, b))
       + Set_Size_4217(Set_Intersection_4217(a, b)));

axiom (forall a: Set_4217, b: Set_4217 :: 
  { Set_Union_4217(a, b) } { Set_Intersection_4217(a, b) } 
  Set_Size_4217(Set_Union_4217(a, b)) + Set_Size_4217(Set_Intersection_4217(a, b))
     == Set_Size_4217(a) + Set_Size_4217(b));

axiom (forall a: [int]bool :: 
  { Choice_1255(a) } 
  a == MapConst_5_1296(false) || a[Choice_1255(a)]);

axiom (forall a: [Permission]bool :: 
  { Choice_3338(a) } 
  a == MapConst_5_3338(false) || a[Choice_3338(a)]);

function {:builtin "MapConst"} MapConst_3_4217(int) : [Permission]int;

function {:builtin "MapEq"} MapEq_4217_3([Permission]int, [Permission]int) : [Permission]bool;

function {:builtin "MapAdd"} MapAdd_4217([Permission]int, [Permission]int) : [Permission]int;

function {:builtin "MapIte"} MapIte_4217_3([Permission]bool, [Permission]int, [Permission]int) : [Permission]int;

function {:builtin "MapLe"} MapLe_4217([Permission]int, [Permission]int) : [Permission]bool;

function {:inline} Set_Collector_4217(a: Set_4217) : [Permission]bool
{
  a->val
}

function {:inline} One_Collector_4689(a: One_4689) : [Permission]bool
{
  MapOne_4689(a->val)
}

function {:inline} MapOne_4689(t: Permission) : [Permission]bool
{
  MapConst_5_3338(false)[t := true]
}

function {:inline} Collector_read_f_Permission(target: read_f) : [Permission]bool
{
  (if target is read_f
     then MapOr_4217(One_Collector_4689(target->perm), MapConst_5_3338(false))
     else MapConst_5_3338(false))
}

function {:builtin "MapAdd"} MapAdd_9125([main_f]int, [main_f]int) : [main_f]int;

function {:builtin "MapConst"} MapConst_3_9136(int) : [main_f]int;

function {:builtin "MapIte"} MapIte_9143_3([main_f]bool, [main_f]int, [main_f]int) : [main_f]int;

function {:builtin "MapAdd"} MapAdd_9157([main_f']int, [main_f']int) : [main_f']int;

function {:builtin "MapConst"} MapConst_3_9168(int) : [main_f']int;

function {:builtin "MapIte"} MapIte_9175_3([main_f']bool, [main_f']int, [main_f']int) : [main_f']int;

function {:builtin "MapAdd"} MapAdd_9189([read_f]int, [read_f]int) : [read_f]int;

function {:builtin "MapConst"} MapConst_3_9200(int) : [read_f]int;

function {:builtin "MapIte"} MapIte_9207_3([read_f]bool, [read_f]int, [read_f]int) : [read_f]int;

datatype Choice_Inv_f {
  Choice_Inv_f_read_f(read_f: read_f)
}

function Trigger_write_x(x: StampedValue) : bool;

function Trigger_main_f'_snapshot(snapshot: [int]StampedValue) : bool;

function Trigger_main_f'_inline$ChannelSend$0$tid(inline$ChannelSend$0$tid: Tid) : bool;

function Trigger_main_f'_inline$ChannelSend$0$snapshot(inline$ChannelSend$0$snapshot: [int]StampedValue) : bool;

function Trigger_main_f'_inline$ChannelSend$0$channels(inline$ChannelSend$0$channels: [Tid]Option_4235) : bool;

function Trigger_read_f_k(k: int) : bool;

function Trigger_read_f_v(v: Value) : bool;

function Trigger_read_f_inline$ChannelSend$0$tid(inline$ChannelSend$0$tid: Tid) : bool;

function Trigger_read_f_inline$ChannelSend$0$snapshot(inline$ChannelSend$0$snapshot: [int]StampedValue) : bool;

function Trigger_read_f_inline$ChannelSend$0$channels(inline$ChannelSend$0$channels: [Tid]Option_4235) : bool;

function Trigger_Inv_f_j(j: int) : bool;

function Trigger_Inv_f_sps'(sps': Set_4217) : bool;

function Trigger_Inv_f_done_set(done_set: Set_4217) : bool;

function Trigger_Inv_f_choice(choice: read_f) : bool;

function Trigger_Inv_f_inline$ChannelSend$0$tid(inline$ChannelSend$0$tid: Tid) : bool;

function Trigger_Inv_f_inline$ChannelSend$0$snapshot(inline$ChannelSend$0$snapshot: [int]StampedValue) : bool;

function Trigger_Inv_f_inline$ChannelSend$0$channels(inline$ChannelSend$0$channels: [Tid]Option_4235) : bool;

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
      Civl_old_pSet: Set_4217, 
      Civl_old_channels: [Tid]Option_4235, 
      Civl_old_snapshots: [Tid][int]StampedValue, 
      Civl_mem: [int]StampedValue, 
      Civl_pSet: Set_4217, 
      Civl_channels: [Tid]Option_4235, 
      Civl_snapshots: [Tid][int]StampedValue :: 
    Civl_mem == Civl_old_mem[i := StampedValue(Civl_old_mem[i]->ts + 1, v)])
}

implementation ChannelSend(tid: Tid, snapshot: [int]StampedValue)
{
  /*** structured program:
    assert Set_IsSubset_3338(WholeTidPermission(tid), pSet);
    assert channels[tid] == None_4235();
    channels[tid] := Some_4235(snapshot);
  **** end structured program */

  anon0:
    channels[tid] := Some_4235(snapshot);
    return;
}



procedure {:inline 1} ChannelSend(tid: Tid, snapshot: [int]StampedValue);
  modifies channels;



function {:inline} Civl_InputOutputRelation_ChannelSend(tid: Tid, snapshot: [int]StampedValue) : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_pSet: Set_4217, 
      Civl_old_channels: [Tid]Option_4235, 
      Civl_old_snapshots: [Tid][int]StampedValue, 
      Civl_mem: [int]StampedValue, 
      Civl_pSet: Set_4217, 
      Civl_channels: [Tid]Option_4235, 
      Civl_snapshots: [Tid][int]StampedValue :: 
    Civl_old_channels[tid] == None_4235()
       && Set_IsSubset_3338(WholeTidPermission(tid), Civl_old_pSet)
       && Civl_channels == Civl_old_channels[tid := Some_4235(snapshot)])
}

implementation main_f'(tid: Tid, sps: Set_4217)
{
  var snapshot: [int]StampedValue;
  var inline$ChannelSend$0$tid: Tid;
  var inline$ChannelSend$0$snapshot: [int]StampedValue;
  var inline$ChannelSend$0$channels: [Tid]Option_4235;

  /*** structured program:
    assume {:add_to_pool "A", 0, n} true;
    assert sps == WholeTidPermission(tid);
    assert channels[tid] == None_4235();
    assume (forall i: int :: 
      1 <= i && i <= n ==> snapshot[i]->ts < mem[i]->ts || snapshot[i] == mem[i]);
    call Set_Put_3326(pSet, sps);
    call ChannelSend(tid, snapshot);
  **** end structured program */

  anon0:
    assume Trigger_main_f'_snapshot(snapshot);
    assume {:add_to_pool "A", 0, n} true;
    assume (forall i: int :: 
      1 <= i && i <= n ==> snapshot[i]->ts < mem[i]->ts || snapshot[i] == mem[i]);
    pSet := Set_Union_4217(pSet, sps);
    goto inline$ChannelSend$0$Entry;

  inline$ChannelSend$0$Entry:
    inline$ChannelSend$0$tid := tid;
    inline$ChannelSend$0$snapshot := snapshot;
    inline$ChannelSend$0$channels := channels;
    goto inline$ChannelSend$0$anon0;

  inline$ChannelSend$0$anon0:
    channels[inline$ChannelSend$0$tid] := Some_4235(inline$ChannelSend$0$snapshot);
    goto inline$ChannelSend$0$Return;

  inline$ChannelSend$0$Return:
    goto anon0$1;

  anon0$1:
    return;
}



procedure {:inline 1} main_f'(tid: Tid, sps: Set_4217);
  modifies pSet, channels;



function {:inline} Civl_InputOutputRelation_main_f'(tid: Tid, sps: Set_4217) : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_pSet: Set_4217, 
      Civl_old_channels: [Tid]Option_4235, 
      Civl_old_snapshots: [Tid][int]StampedValue, 
      Civl_mem: [int]StampedValue, 
      Civl_pSet: Set_4217, 
      Civl_channels: [Tid]Option_4235, 
      Civl_snapshots: [Tid][int]StampedValue :: 
    (forall snapshot: [int]StampedValue :: 
        true
           ==> 
          (forall i: int :: 
            1 <= i && i <= n
               ==> snapshot[i]->ts < Civl_old_mem[i]->ts || snapshot[i] == Civl_old_mem[i])
           ==> Civl_old_channels[tid] == None_4235())
       && (forall snapshot: [int]StampedValue :: 
        true
           ==> 
          (forall i: int :: 
            1 <= i && i <= n
               ==> snapshot[i]->ts < Civl_old_mem[i]->ts || snapshot[i] == Civl_old_mem[i])
           ==> Set_IsSubset_3338(WholeTidPermission(tid), Set_Union_4217(Civl_old_pSet, sps)))
       && (true ==> Civl_old_channels[tid] == None_4235())
       && (true ==> sps == WholeTidPermission(tid))
       && (exists Civl_snapshot#0: [int]StampedValue :: 
        true
           && (forall i: int :: 
            1 <= i && i <= n
               ==> Civl_snapshot#0[i]->ts < Civl_mem[i]->ts || Civl_snapshot#0[i] == Civl_mem[i])
           && Civl_pSet == Set_Union_4217(Civl_old_pSet, sps)
           && Civl_channels == Civl_old_channels[tid := Some_4235(Civl_snapshot#0)]))
}

implementation read_f(perm: One_4689)
{
  var {:pool "K"} k: int;
  var {:pool "V"} v: Value;
  var inline$ChannelSend$0$tid: Tid;
  var inline$ChannelSend$0$snapshot: [int]StampedValue;
  var inline$ChannelSend$0$channels: [Tid]Option_4235;

  /*** structured program:
    assert 1 <= perm->val->mem_index && perm->val->mem_index <= n;
    assert channels[perm->val->tid] == None_4235();
    assume {:add_to_pool "A", 0, n} true;
    if (*)
    {
        assume {:add_to_pool "K", mem[perm->val->mem_index]->ts, k} {:add_to_pool "V", mem[perm->val->mem_index]->value, v} true;
        assume k < mem[perm->val->mem_index]->ts;
        snapshots[perm->val->tid][perm->val->mem_index] := StampedValue(k, v);
    }
    else
    {
        snapshots[perm->val->tid][perm->val->mem_index] := mem[perm->val->mem_index];
    }

    call One_Put_3326(pSet, perm);
    if (Set_IsSubset(WholeTidPermission(perm->val->tid), pSet))
    {
        call ChannelSend(perm->val->tid, snapshots[perm->val->tid]);
    }
  **** end structured program */

  anon0:
    assume Trigger_read_f_v(v);
    assume Trigger_read_f_k(k);
    assume {:add_to_pool "A", 0, n} true;
    goto anon5_Then, anon5_Else;

  anon5_Else:
    snapshots[perm->val->tid][perm->val->mem_index] := mem[perm->val->mem_index];
    goto anon3;

  anon3:
    pSet := Set_Add_3326(pSet, perm->val);
    goto anon6_Then, anon6_Else;

  anon6_Else:
    assume {:partition} !Set_IsSubset_3338(WholeTidPermission(perm->val->tid), pSet);
    return;

  anon6_Then:
    assume {:partition} Set_IsSubset_3338(WholeTidPermission(perm->val->tid), pSet);
    goto inline$ChannelSend$0$Entry;

  inline$ChannelSend$0$Entry:
    inline$ChannelSend$0$tid := perm->val->tid;
    inline$ChannelSend$0$snapshot := snapshots[perm->val->tid];
    inline$ChannelSend$0$channels := channels;
    goto inline$ChannelSend$0$anon0;

  inline$ChannelSend$0$anon0:
    channels[inline$ChannelSend$0$tid] := Some_4235(inline$ChannelSend$0$snapshot);
    goto inline$ChannelSend$0$Return;

  inline$ChannelSend$0$Return:
    goto anon6_Then$1;

  anon6_Then$1:
    return;

  anon5_Then:
    assume {:add_to_pool "K", mem[perm->val->mem_index]->ts, k} {:add_to_pool "V", mem[perm->val->mem_index]->value, v} true;
    assume k < mem[perm->val->mem_index]->ts;
    snapshots[perm->val->tid][perm->val->mem_index] := StampedValue(k, v);
    goto anon3;
}



procedure {:inline 1} read_f(perm: One_4689);
  modifies snapshots, pSet, channels;



function {:inline} Civl_InputOutputRelation_read_f(perm: One_4689) : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_pSet: Set_4217, 
      Civl_old_channels: [Tid]Option_4235, 
      Civl_old_snapshots: [Tid][int]StampedValue, 
      Civl_mem: [int]StampedValue, 
      Civl_pSet: Set_4217, 
      Civl_channels: [Tid]Option_4235, 
      Civl_snapshots: [Tid][int]StampedValue :: 
    (forall k: int :: 
        true
           ==> 
          true
           ==> 
          k < Civl_old_mem[perm->val->mem_index]->ts
           ==> 
          Set_IsSubset_3338(WholeTidPermission(perm->val->tid), Set_Add_3326(Civl_old_pSet, perm->val))
           ==> Civl_old_channels[perm->val->tid] == None_4235())
       && (forall k: int :: 
        true
           ==> 
          true
           ==> 
          k < Civl_old_mem[perm->val->mem_index]->ts
           ==> 
          Set_IsSubset_3338(WholeTidPermission(perm->val->tid), Set_Add_3326(Civl_old_pSet, perm->val))
           ==> Set_IsSubset_3338(WholeTidPermission(perm->val->tid), Set_Add_3326(Civl_old_pSet, perm->val)))
       && (true
         ==> 
        Set_IsSubset_3338(WholeTidPermission(perm->val->tid), Set_Add_3326(Civl_old_pSet, perm->val))
         ==> Civl_old_channels[perm->val->tid] == None_4235())
       && (true
         ==> 
        Set_IsSubset_3338(WholeTidPermission(perm->val->tid), Set_Add_3326(Civl_old_pSet, perm->val))
         ==> Set_IsSubset_3338(WholeTidPermission(perm->val->tid), Set_Add_3326(Civl_old_pSet, perm->val)))
       && Civl_old_channels[perm->val->tid] == None_4235()
       && 
      1 <= perm->val->mem_index
       && perm->val->mem_index <= n
       && (
        (exists {:pool "K"} Civl_k#0: int, {:pool "V"} Civl_v#0: Value :: 
          true
             && true
             && Civl_k#0 < Civl_mem[perm->val->mem_index]->ts
             && Set_IsSubset_3338(WholeTidPermission(perm->val->tid), Civl_pSet)
             && Civl_snapshots
               == Civl_old_snapshots[perm->val->tid := Civl_old_snapshots[perm->val->tid][perm->val->mem_index := StampedValue(Civl_k#0, Civl_v#0)]]
             && Civl_pSet == Set_Add_3326(Civl_old_pSet, perm->val)
             && Civl_channels
               == Civl_old_channels[perm->val->tid := Some_4235(Civl_snapshots[perm->val->tid])])
         || (exists {:pool "K"} Civl_k#0: int, {:pool "V"} Civl_v#0: Value :: 
          true
             && true
             && Civl_k#0 < Civl_mem[perm->val->mem_index]->ts
             && !Set_IsSubset_3338(WholeTidPermission(perm->val->tid), Civl_pSet)
             && Civl_snapshots
               == Civl_old_snapshots[perm->val->tid := Civl_old_snapshots[perm->val->tid][perm->val->mem_index := StampedValue(Civl_k#0, Civl_v#0)]]
             && Civl_pSet == Set_Add_3326(Civl_old_pSet, perm->val)
             && Civl_channels == Civl_old_channels)
         || (
          true
           && Set_IsSubset_3338(WholeTidPermission(perm->val->tid), Civl_pSet)
           && Civl_snapshots
             == Civl_old_snapshots[perm->val->tid := Civl_old_snapshots[perm->val->tid][perm->val->mem_index := Civl_mem[perm->val->mem_index]]]
           && Civl_pSet == Set_Add_3326(Civl_old_pSet, perm->val)
           && Civl_channels
             == Civl_old_channels[perm->val->tid := Some_4235(Civl_snapshots[perm->val->tid])])
         || (
          true
           && !Set_IsSubset_3338(WholeTidPermission(perm->val->tid), Civl_pSet)
           && Civl_snapshots
             == Civl_old_snapshots[perm->val->tid := Civl_old_snapshots[perm->val->tid][perm->val->mem_index := Civl_mem[perm->val->mem_index]]]
           && Civl_pSet == Set_Add_3326(Civl_old_pSet, perm->val)
           && Civl_channels == Civl_old_channels)))
}

implementation Inv_f(tid: Tid, sps: Set_4217) returns (Civl_PAs_read_f: [read_f]int)
{
  var {:pool "A"} j: int;
  var sps': Set_4217;
  var done_set: Set_4217;
  var choice: read_f;
  var inline$ChannelSend$0$tid: Tid;
  var inline$ChannelSend$0$snapshot: [int]StampedValue;
  var inline$ChannelSend$0$channels: [Tid]Option_4235;

  /*** structured program:
    assert sps == WholeTidPermission(tid);
    assert channels[tid] == None_4235();
    assume {:add_to_pool "A", 0, j + 1, n} 0 <= j && j <= n;
    havoc snapshots;
    assume (forall i: int :: 
      1 <= i && i <= j
         ==> snapshots[tid][i]->ts < mem[i]->ts || snapshots[tid][i] == mem[i]);
    assume {:add_to_pool "D", Permission(tid, n)} true;
    sps' := sps;
    call done_set := Set_Get_3391(sps', (lambda {:pool "D"} x: Permission :: 
      x->tid == tid && 1 <= x->mem_index && x->mem_index <= j));
    call Set_Put_3326(pSet, done_set);
    if (j < n)
    {
        choice := read_f(One_4689(Permission(tid, j + 1)));
        assume {:add_to_pool "C", choice} true;
        call create_asyncs((lambda {:pool "C"} pa: read_f :: 
          j + 1 <= pa->perm->val->mem_index
             && pa->perm->val->mem_index <= n
             && pa->perm->val->tid == tid));
        call set_choice(choice);
    }
    else
    {
        call ChannelSend(tid, snapshots[tid]);
    }
  **** end structured program */

  anon0:
    assume Trigger_Inv_f_j(j);
    Civl_PAs_read_f := MapConst_3_9200(0);
    assume {:add_to_pool "A", 0, j + 1, n} 0 <= j && j <= n;
    havoc snapshots;
    assume (forall i: int :: 
      1 <= i && i <= j
         ==> snapshots[tid][i]->ts < mem[i]->ts || snapshots[tid][i] == mem[i]);
    assume {:add_to_pool "D", Permission(tid, n)} true;
    sps' := sps;
    done_set := Set_4217((lambda {:pool "D"} x: Permission :: 
        x->tid == tid && 1 <= x->mem_index && x->mem_index <= j));
    sps' := Set_Difference_4217(sps', done_set);
    pSet := Set_Union_4217(pSet, done_set);
    goto anon3_Then, anon3_Else;

  anon3_Else:
    assume {:partition} n <= j;
    goto inline$ChannelSend$0$Entry;

  inline$ChannelSend$0$Entry:
    inline$ChannelSend$0$tid := tid;
    inline$ChannelSend$0$snapshot := snapshots[tid];
    inline$ChannelSend$0$channels := channels;
    goto inline$ChannelSend$0$anon0;

  inline$ChannelSend$0$anon0:
    channels[inline$ChannelSend$0$tid] := Some_4235(inline$ChannelSend$0$snapshot);
    goto inline$ChannelSend$0$Return;

  inline$ChannelSend$0$Return:
    goto anon3_Else$1;

  anon3_Else$1:
    return;

  anon3_Then:
    assume {:partition} j < n;
    choice := read_f(One_4689(Permission(tid, j + 1)));
    assume {:add_to_pool "C", choice} true;
    Civl_PAs_read_f := MapAdd_9189(Civl_PAs_read_f, 
      MapIte_9207_3((lambda {:pool "C"} pa: read_f :: 
          j + 1 <= pa->perm->val->mem_index
             && pa->perm->val->mem_index <= n
             && pa->perm->val->tid == tid), 
        MapConst_3_9200(1), 
        MapConst_3_9200(0)));
    return;
}



procedure {:inline 1} Inv_f(tid: Tid, sps: Set_4217) returns (Civl_PAs_read_f: [read_f]int);
  modifies snapshots, pSet, channels;



function {:inline} Civl_InputOutputRelation_Inv_f(tid: Tid, sps: Set_4217, Civl_PAs_read_f: [read_f]int) : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_pSet: Set_4217, 
      Civl_old_channels: [Tid]Option_4235, 
      Civl_old_snapshots: [Tid][int]StampedValue, 
      Civl_mem: [int]StampedValue, 
      Civl_pSet: Set_4217, 
      Civl_channels: [Tid]Option_4235, 
      Civl_snapshots: [Tid][int]StampedValue :: 
    (forall j: int :: 
        0 <= j && j <= n
           ==> (forall snapshots: [Tid][int]StampedValue :: 
            (forall i: int :: 
                1 <= i && i <= j
                   ==> snapshots[tid][i]->ts < Civl_old_mem[i]->ts
                     || snapshots[tid][i] == Civl_old_mem[i])
               ==> 
              true
               ==> 
              n <= j
               ==> Civl_old_channels[tid] == None_4235()))
       && (forall j: int :: 
        0 <= j && j <= n
           ==> (forall snapshots: [Tid][int]StampedValue :: 
            (forall i: int :: 
                1 <= i && i <= j
                   ==> snapshots[tid][i]->ts < Civl_old_mem[i]->ts
                     || snapshots[tid][i] == Civl_old_mem[i])
               ==> 
              true
               ==> 
              n <= j
               ==> Set_IsSubset_3338(WholeTidPermission(tid), 
                Set_Union_4217(Civl_old_pSet, 
                  Set_4217((lambda {:pool "D"} x: Permission :: 
                      x->tid == tid && 1 <= x->mem_index && x->mem_index <= j))))))
       && (forall j: int :: 
        0 <= j && j <= n
           ==> (forall snapshots: [Tid][int]StampedValue :: 
            (forall i: int :: 
                1 <= i && i <= j
                   ==> snapshots[tid][i]->ts < Civl_old_mem[i]->ts
                     || snapshots[tid][i] == Civl_old_mem[i])
               ==> 
              true
               ==> Set_IsSubset_3338(Set_4217((lambda {:pool "D"} x: Permission :: 
                    x->tid == tid && 1 <= x->mem_index && x->mem_index <= j)), 
                sps)))
       && Civl_old_channels[tid] == None_4235()
       && sps == WholeTidPermission(tid)
       && ((exists {:pool "A"} Civl_j#0: int :: 
          0 <= Civl_j#0
             && Civl_j#0 <= n
             && (forall i: int :: 
              1 <= i && i <= Civl_j#0
                 ==> Civl_snapshots[tid][i]->ts < Civl_mem[i]->ts
                   || Civl_snapshots[tid][i] == Civl_mem[i])
             && true
             && Civl_j#0 < n
             && true
             && Civl_pSet
               == Set_Union_4217(Civl_old_pSet, 
                Set_4217((lambda {:pool "D"} x: Permission :: 
                    x->tid == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
             && Civl_PAs_read_f
               == MapAdd_9189(MapConst_3_9200(0), 
                MapIte_9207_3((lambda {:pool "C"} pa: read_f :: 
                    Civl_j#0 + 1 <= pa->perm->val->mem_index
                       && pa->perm->val->mem_index <= n
                       && pa->perm->val->tid == tid), 
                  MapConst_3_9200(1), 
                  MapConst_3_9200(0)))
             && Civl_channels == Civl_old_channels)
         || (exists {:pool "A"} Civl_j#0: int :: 
          0 <= Civl_j#0
             && Civl_j#0 <= n
             && (forall i: int :: 
              1 <= i && i <= Civl_j#0
                 ==> Civl_snapshots[tid][i]->ts < Civl_mem[i]->ts
                   || Civl_snapshots[tid][i] == Civl_mem[i])
             && true
             && n <= Civl_j#0
             && Civl_PAs_read_f == MapConst_3_9200(0)
             && Civl_pSet
               == Set_Union_4217(Civl_old_pSet, 
                Set_4217((lambda {:pool "D"} x: Permission :: 
                    x->tid == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
             && Civl_channels == Civl_old_channels[tid := Some_4235(Civl_snapshots[tid])])))
}

implementation Inv_f_With_Choice(tid: Tid, sps: Set_4217)
   returns (Civl_PAs_read_f: [read_f]int, Civl_choice: Choice_Inv_f)
{
  var {:pool "A"} j: int;
  var sps': Set_4217;
  var done_set: Set_4217;
  var choice: read_f;
  var inline$ChannelSend$0$tid: Tid;
  var inline$ChannelSend$0$snapshot: [int]StampedValue;
  var inline$ChannelSend$0$channels: [Tid]Option_4235;

  /*** structured program:
    assert sps == WholeTidPermission(tid);
    assert channels[tid] == None_4235();
    assume {:add_to_pool "A", 0, j + 1, n} 0 <= j && j <= n;
    havoc snapshots;
    assume (forall i: int :: 
      1 <= i && i <= j
         ==> snapshots[tid][i]->ts < mem[i]->ts || snapshots[tid][i] == mem[i]);
    assume {:add_to_pool "D", Permission(tid, n)} true;
    sps' := sps;
    call done_set := Set_Get_3391(sps', (lambda {:pool "D"} x: Permission :: 
      x->tid == tid && 1 <= x->mem_index && x->mem_index <= j));
    call Set_Put_3326(pSet, done_set);
    if (j < n)
    {
        choice := read_f(One_4689(Permission(tid, j + 1)));
        assume {:add_to_pool "C", choice} true;
        call create_asyncs((lambda {:pool "C"} pa: read_f :: 
          j + 1 <= pa->perm->val->mem_index
             && pa->perm->val->mem_index <= n
             && pa->perm->val->tid == tid));
        call set_choice(choice);
    }
    else
    {
        call ChannelSend(tid, snapshots[tid]);
    }
  **** end structured program */

  anon0:
    Civl_PAs_read_f := MapConst_3_9200(0);
    assert sps == WholeTidPermission(tid);
    assert channels[tid] == None_4235();
    assume {:add_to_pool "A", 0, j + 1, n} 0 <= j && j <= n;
    havoc snapshots;
    assume (forall i: int :: 
      1 <= i && i <= j
         ==> snapshots[tid][i]->ts < mem[i]->ts || snapshots[tid][i] == mem[i]);
    assume {:add_to_pool "D", Permission(tid, n)} true;
    sps' := sps;
    done_set := Set_4217((lambda {:pool "D"} x: Permission :: 
        x->tid == tid && 1 <= x->mem_index && x->mem_index <= j));
    assert Set_IsSubset_3338(done_set, sps');
    sps' := Set_Difference_4217(sps', done_set);
    pSet := Set_Union_4217(pSet, done_set);
    goto anon3_Then, anon3_Else;

  anon3_Else:
    assume {:partition} n <= j;
    goto inline$ChannelSend$0$Entry;

  inline$ChannelSend$0$Entry:
    inline$ChannelSend$0$tid := tid;
    inline$ChannelSend$0$snapshot := snapshots[tid];
    inline$ChannelSend$0$channels := channels;
    goto inline$ChannelSend$0$anon0;

  inline$ChannelSend$0$anon0:
    assert Set_IsSubset_3338(WholeTidPermission(inline$ChannelSend$0$tid), pSet);
    assert channels[inline$ChannelSend$0$tid] == None_4235();
    channels[inline$ChannelSend$0$tid] := Some_4235(inline$ChannelSend$0$snapshot);
    goto inline$ChannelSend$0$Return;

  inline$ChannelSend$0$Return:
    goto anon3_Else$1;

  anon3_Else$1:
    return;

  anon3_Then:
    assume {:partition} j < n;
    choice := read_f(One_4689(Permission(tid, j + 1)));
    assume {:add_to_pool "C", choice} true;
    Civl_PAs_read_f := MapAdd_9189(Civl_PAs_read_f, 
      MapIte_9207_3((lambda {:pool "C"} pa: read_f :: 
          j + 1 <= pa->perm->val->mem_index
             && pa->perm->val->mem_index <= n
             && pa->perm->val->tid == tid), 
        MapConst_3_9200(1), 
        MapConst_3_9200(0)));
    assert Civl_PAs_read_f == MapConst_3_9200(0) || Civl_PAs_read_f[choice] > 0;
    Civl_choice->read_f := choice;
    return;
}



procedure {:inline 1} Inv_f_With_Choice(tid: Tid, sps: Set_4217)
   returns (Civl_PAs_read_f: [read_f]int, Civl_choice: Choice_Inv_f);
  modifies snapshots, pSet, channels;



function {:inline} Civl_InputOutputRelation_Inv_f_With_Choice(tid: Tid, sps: Set_4217, Civl_PAs_read_f: [read_f]int, Civl_choice: Choice_Inv_f)
   : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_pSet: Set_4217, 
      Civl_old_channels: [Tid]Option_4235, 
      Civl_old_snapshots: [Tid][int]StampedValue, 
      Civl_mem: [int]StampedValue, 
      Civl_pSet: Set_4217, 
      Civl_channels: [Tid]Option_4235, 
      Civl_snapshots: [Tid][int]StampedValue :: 
    (forall j: int :: 
        0 <= j && j <= n
           ==> (forall snapshots: [Tid][int]StampedValue :: 
            (forall i: int :: 
                1 <= i && i <= j
                   ==> snapshots[tid][i]->ts < Civl_old_mem[i]->ts
                     || snapshots[tid][i] == Civl_old_mem[i])
               ==> 
              true
               ==> 
              n <= j
               ==> Civl_old_channels[tid] == None_4235()))
       && (forall j: int :: 
        0 <= j && j <= n
           ==> (forall snapshots: [Tid][int]StampedValue :: 
            (forall i: int :: 
                1 <= i && i <= j
                   ==> snapshots[tid][i]->ts < Civl_old_mem[i]->ts
                     || snapshots[tid][i] == Civl_old_mem[i])
               ==> 
              true
               ==> 
              n <= j
               ==> Set_IsSubset_3338(WholeTidPermission(tid), 
                Set_Union_4217(Civl_old_pSet, 
                  Set_4217((lambda {:pool "D"} x: Permission :: 
                      x->tid == tid && 1 <= x->mem_index && x->mem_index <= j))))))
       && (forall j: int :: 
        0 <= j && j <= n
           ==> (forall snapshots: [Tid][int]StampedValue :: 
            (forall i: int :: 
                1 <= i && i <= j
                   ==> snapshots[tid][i]->ts < Civl_old_mem[i]->ts
                     || snapshots[tid][i] == Civl_old_mem[i])
               ==> 
              true
               ==> Set_IsSubset_3338(Set_4217((lambda {:pool "D"} x: Permission :: 
                    x->tid == tid && 1 <= x->mem_index && x->mem_index <= j)), 
                sps)))
       && Civl_old_channels[tid] == None_4235()
       && sps == WholeTidPermission(tid)
       && ((exists {:pool "A"} Civl_j#0: int :: 
          sps == WholeTidPermission(tid)
             && Civl_channels[tid] == None_4235()
             && 0 <= Civl_j#0
             && Civl_j#0 <= n
             && (forall i: int :: 
              1 <= i && i <= Civl_j#0
                 ==> Civl_snapshots[tid][i]->ts < Civl_mem[i]->ts
                   || Civl_snapshots[tid][i] == Civl_mem[i])
             && true
             && Set_IsSubset_3338(Set_4217((lambda {:pool "D"} x: Permission :: 
                  x->tid == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)), 
              sps)
             && Civl_j#0 < n
             && true
             && (Civl_PAs_read_f == MapConst_3_9200(0)
               || Civl_PAs_read_f[read_f(One_4689(Permission(tid, Civl_j#0 + 1)))] > 0)
             && Civl_pSet
               == Set_Union_4217(Civl_old_pSet, 
                Set_4217((lambda {:pool "D"} x: Permission :: 
                    x->tid == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
             && Civl_PAs_read_f
               == MapAdd_9189(MapConst_3_9200(0), 
                MapIte_9207_3((lambda {:pool "C"} pa: read_f :: 
                    Civl_j#0 + 1 <= pa->perm->val->mem_index
                       && pa->perm->val->mem_index <= n
                       && pa->perm->val->tid == tid), 
                  MapConst_3_9200(1), 
                  MapConst_3_9200(0)))
             && Civl_choice
               == Choice_Inv_f_read_f(read_f(One_4689(Permission(tid, Civl_j#0 + 1))))
             && Civl_channels == Civl_old_channels)
         || (exists {:pool "A"} Civl_j#0: int :: 
          sps == WholeTidPermission(tid)
             && Civl_old_channels[tid] == None_4235()
             && 0 <= Civl_j#0
             && Civl_j#0 <= n
             && (forall i: int :: 
              1 <= i && i <= Civl_j#0
                 ==> Civl_snapshots[tid][i]->ts < Civl_mem[i]->ts
                   || Civl_snapshots[tid][i] == Civl_mem[i])
             && true
             && Set_IsSubset_3338(Set_4217((lambda {:pool "D"} x: Permission :: 
                  x->tid == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)), 
              sps)
             && n <= Civl_j#0
             && Set_IsSubset_3338(WholeTidPermission(tid), Civl_pSet)
             && Civl_old_channels[tid] == None_4235()
             && Civl_PAs_read_f == MapConst_3_9200(0)
             && Civl_pSet
               == Set_Union_4217(Civl_old_pSet, 
                Set_4217((lambda {:pool "D"} x: Permission :: 
                    x->tid == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
             && Civl_channels == Civl_old_channels[tid := Some_4235(Civl_snapshots[tid])])))
}

implementation main_f(tid: Tid, sps: Set_4217) returns (Civl_PAs_read_f: [read_f]int)
{
  /*** structured program:
    assume {:add_to_pool "A", 0, n} true;
    assert sps == WholeTidPermission(tid);
    assert channels[tid] == None_4235();
    call create_asyncs_3363((lambda pa: read_f :: 
      1 <= pa->perm->val->mem_index
         && pa->perm->val->mem_index <= n
         && pa->perm->val->tid == tid));
  **** end structured program */

  anon0:
    Civl_PAs_read_f := MapConst_3_9200(0);
    assume {:add_to_pool "A", 0, n} true;
    Civl_PAs_read_f := MapAdd_9189(Civl_PAs_read_f, 
      MapIte_9207_3((lambda pa: read_f :: 
          1 <= pa->perm->val->mem_index
             && pa->perm->val->mem_index <= n
             && pa->perm->val->tid == tid), 
        MapConst_3_9200(1), 
        MapConst_3_9200(0)));
    return;
}



procedure {:inline 1} main_f(tid: Tid, sps: Set_4217) returns (Civl_PAs_read_f: [read_f]int);
  modifies pSet;



function {:inline} Civl_InputOutputRelation_main_f(tid: Tid, sps: Set_4217, Civl_PAs_read_f: [read_f]int) : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_pSet: Set_4217, 
      Civl_old_channels: [Tid]Option_4235, 
      Civl_old_snapshots: [Tid][int]StampedValue, 
      Civl_mem: [int]StampedValue, 
      Civl_pSet: Set_4217, 
      Civl_channels: [Tid]Option_4235, 
      Civl_snapshots: [Tid][int]StampedValue :: 
    (true ==> Civl_old_channels[tid] == None_4235())
       && (true ==> sps == WholeTidPermission(tid))
       && 
      true
       && Civl_PAs_read_f
         == MapAdd_9189(MapConst_3_9200(0), 
          MapIte_9207_3((lambda pa: read_f :: 
              1 <= pa->perm->val->mem_index
                 && pa->perm->val->mem_index <= n
                 && pa->perm->val->tid == tid), 
            MapConst_3_9200(1), 
            MapConst_3_9200(0)))
       && Civl_pSet == Civl_old_pSet)
}

implementation Civl_CommutativityChecker_read_f_write_1(first_perm: One_4689, second_i: int, second_v: Value)
{

  init:
    call read_f(first_perm);
    call write(second_i, second_v);
    assert true
       ==> (exists {:pool "K"} Civl_first_k#0: int, {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), pSet)
             && mem == old(mem)[second_i := StampedValue(old(mem)[second_i]->ts + 1, second_v)]
             && snapshots
               == old(snapshots)[first_perm->val->tid := old(snapshots)[first_perm->val->tid][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3326(old(pSet), first_perm->val)
             && channels
               == old(channels)[first_perm->val->tid := Some_4235(snapshots[first_perm->val->tid])])
         || (exists {:pool "K"} Civl_first_k#0: int, {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && !Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), pSet)
             && mem == old(mem)[second_i := StampedValue(old(mem)[second_i]->ts + 1, second_v)]
             && snapshots
               == old(snapshots)[first_perm->val->tid := old(snapshots)[first_perm->val->tid][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3326(old(pSet), first_perm->val)
             && channels == old(channels))
         || (
          true
           && Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), pSet)
           && mem == old(mem)[second_i := StampedValue(old(mem)[second_i]->ts + 1, second_v)]
           && snapshots
             == old(snapshots)[first_perm->val->tid := old(snapshots)[first_perm->val->tid][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet == Set_Add_3326(old(pSet), first_perm->val)
           && channels
             == old(channels)[first_perm->val->tid := Some_4235(snapshots[first_perm->val->tid])])
         || (
          true
           && !Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), pSet)
           && mem == old(mem)[second_i := StampedValue(old(mem)[second_i]->ts + 1, second_v)]
           && snapshots
             == old(snapshots)[first_perm->val->tid := old(snapshots)[first_perm->val->tid][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet == Set_Add_3326(old(pSet), first_perm->val)
           && channels == old(channels));
    return;
}



procedure Civl_CommutativityChecker_read_f_write_1(first_perm: One_4689, second_i: int, second_v: Value);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3338(One_Collector_4689(first_perm), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(0)))
         == MapConst_5_3338(true)
       && MapImp_3338(Set_Collector_4217(pSet), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(1)))
         == MapConst_5_3338(true));
  requires (forall first_k: int :: 
    true
       ==> 
      true
       ==> 
      first_k < mem[first_perm->val->mem_index]->ts
       ==> 
      Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val))
       ==> channels[first_perm->val->tid] == None_4235());
  requires (forall first_k: int :: 
    true
       ==> 
      true
       ==> 
      first_k < mem[first_perm->val->mem_index]->ts
       ==> 
      Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val))
       ==> Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val)));
  requires true
     ==> 
    Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val))
     ==> channels[first_perm->val->tid] == None_4235();
  requires true
     ==> 
    Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val))
     ==> Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val));
  requires channels[first_perm->val->tid] == None_4235();
  requires 1 <= first_perm->val->mem_index && first_perm->val->mem_index <= n;
  requires !Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val));
  modifies mem, pSet, channels, snapshots;



implementation Civl_CommutativityChecker_read_f_read_f_1(first_perm: One_4689, second_perm: One_4689)
{

  init:
    call read_f(first_perm);
    call read_f(second_perm);
    assert true
       ==> (exists {:pool "K"} Civl_second_k#0: int, 
            {:pool "K"} Civl_first_k#0: int, 
            {:pool "V"} Civl_second_v#0: Value, 
            {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_second_v#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), 
              Set_Add_3326(old(pSet), second_perm->val))
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), pSet)
             && snapshots
               == old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->tid := old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->tid][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3326(Set_Add_3326(old(pSet), second_perm->val), first_perm->val)
             && channels
               == old(channels)[second_perm->val->tid := Some_4235(old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][second_perm->val->tid])][first_perm->val->tid := Some_4235(snapshots[first_perm->val->tid])]
             && mem == old(mem))
         || (exists {:pool "K"} Civl_second_k#0: int, 
            {:pool "K"} Civl_first_k#0: int, 
            {:pool "V"} Civl_second_v#0: Value, 
            {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_second_v#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), 
              Set_Add_3326(old(pSet), second_perm->val))
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && !Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), pSet)
             && channels
               == old(channels)[second_perm->val->tid := Some_4235(old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][second_perm->val->tid])]
             && snapshots
               == old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->tid := old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->tid][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3326(Set_Add_3326(old(pSet), second_perm->val), first_perm->val)
             && mem == old(mem))
         || (exists {:pool "K"} Civl_second_k#0: int, {:pool "V"} Civl_second_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_v(Civl_second_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), 
              Set_Add_3326(old(pSet), second_perm->val))
             && true
             && Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), pSet)
             && snapshots
               == old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->tid := old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->tid][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
             && pSet == Set_Add_3326(Set_Add_3326(old(pSet), second_perm->val), first_perm->val)
             && channels
               == old(channels)[second_perm->val->tid := Some_4235(old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][second_perm->val->tid])][first_perm->val->tid := Some_4235(snapshots[first_perm->val->tid])]
             && mem == old(mem))
         || (exists {:pool "K"} Civl_second_k#0: int, {:pool "V"} Civl_second_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_v(Civl_second_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), 
              Set_Add_3326(old(pSet), second_perm->val))
             && true
             && !Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), pSet)
             && channels
               == old(channels)[second_perm->val->tid := Some_4235(old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][second_perm->val->tid])]
             && snapshots
               == old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->tid := old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->tid][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
             && pSet == Set_Add_3326(Set_Add_3326(old(pSet), second_perm->val), first_perm->val)
             && mem == old(mem))
         || (exists {:pool "K"} Civl_second_k#0: int, 
            {:pool "K"} Civl_first_k#0: int, 
            {:pool "V"} Civl_second_v#0: Value, 
            {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_second_v#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && !Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), 
              Set_Add_3326(old(pSet), second_perm->val))
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), pSet)
             && snapshots
               == old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->tid := old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->tid][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3326(Set_Add_3326(old(pSet), second_perm->val), first_perm->val)
             && channels
               == old(channels)[first_perm->val->tid := Some_4235(snapshots[first_perm->val->tid])]
             && mem == old(mem))
         || (exists {:pool "K"} Civl_second_k#0: int, 
            {:pool "K"} Civl_first_k#0: int, 
            {:pool "V"} Civl_second_v#0: Value, 
            {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_second_v#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && !Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), 
              Set_Add_3326(old(pSet), second_perm->val))
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && !Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), pSet)
             && snapshots
               == old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->tid := old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->tid][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3326(Set_Add_3326(old(pSet), second_perm->val), first_perm->val)
             && mem == old(mem)
             && channels == old(channels))
         || (exists {:pool "K"} Civl_second_k#0: int, {:pool "V"} Civl_second_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_v(Civl_second_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && !Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), 
              Set_Add_3326(old(pSet), second_perm->val))
             && true
             && Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), pSet)
             && snapshots
               == old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->tid := old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->tid][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
             && pSet == Set_Add_3326(Set_Add_3326(old(pSet), second_perm->val), first_perm->val)
             && channels
               == old(channels)[first_perm->val->tid := Some_4235(snapshots[first_perm->val->tid])]
             && mem == old(mem))
         || (exists {:pool "K"} Civl_second_k#0: int, {:pool "V"} Civl_second_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_v(Civl_second_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && !Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), 
              Set_Add_3326(old(pSet), second_perm->val))
             && true
             && !Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), pSet)
             && snapshots
               == old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->tid := old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->tid][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
             && pSet == Set_Add_3326(Set_Add_3326(old(pSet), second_perm->val), first_perm->val)
             && mem == old(mem)
             && channels == old(channels))
         || (exists {:pool "K"} Civl_first_k#0: int, {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), 
              Set_Add_3326(old(pSet), second_perm->val))
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), pSet)
             && snapshots
               == old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->tid := old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->tid][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3326(Set_Add_3326(old(pSet), second_perm->val), first_perm->val)
             && channels
               == old(channels)[second_perm->val->tid := Some_4235(old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][second_perm->val->tid])][first_perm->val->tid := Some_4235(snapshots[first_perm->val->tid])]
             && mem == old(mem))
         || (exists {:pool "K"} Civl_first_k#0: int, {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), 
              Set_Add_3326(old(pSet), second_perm->val))
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && !Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), pSet)
             && channels
               == old(channels)[second_perm->val->tid := Some_4235(old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][second_perm->val->tid])]
             && snapshots
               == old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->tid := old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->tid][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3326(Set_Add_3326(old(pSet), second_perm->val), first_perm->val)
             && mem == old(mem))
         || (
          true
           && Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), 
            Set_Add_3326(old(pSet), second_perm->val))
           && true
           && Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), pSet)
           && snapshots
             == old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->tid := old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->tid][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet == Set_Add_3326(Set_Add_3326(old(pSet), second_perm->val), first_perm->val)
           && channels
             == old(channels)[second_perm->val->tid := Some_4235(old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][second_perm->val->tid])][first_perm->val->tid := Some_4235(snapshots[first_perm->val->tid])]
           && mem == old(mem))
         || (
          true
           && Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), 
            Set_Add_3326(old(pSet), second_perm->val))
           && true
           && !Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), pSet)
           && channels
             == old(channels)[second_perm->val->tid := Some_4235(old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][second_perm->val->tid])]
           && snapshots
             == old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->tid := old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->tid][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet == Set_Add_3326(Set_Add_3326(old(pSet), second_perm->val), first_perm->val)
           && mem == old(mem))
         || (exists {:pool "K"} Civl_first_k#0: int, {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && !Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), 
              Set_Add_3326(old(pSet), second_perm->val))
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), pSet)
             && snapshots
               == old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->tid := old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->tid][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3326(Set_Add_3326(old(pSet), second_perm->val), first_perm->val)
             && channels
               == old(channels)[first_perm->val->tid := Some_4235(snapshots[first_perm->val->tid])]
             && mem == old(mem))
         || (exists {:pool "K"} Civl_first_k#0: int, {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && !Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), 
              Set_Add_3326(old(pSet), second_perm->val))
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && !Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), pSet)
             && snapshots
               == old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->tid := old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->tid][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3326(Set_Add_3326(old(pSet), second_perm->val), first_perm->val)
             && mem == old(mem)
             && channels == old(channels))
         || (
          true
           && !Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), 
            Set_Add_3326(old(pSet), second_perm->val))
           && true
           && Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), pSet)
           && snapshots
             == old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->tid := old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->tid][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet == Set_Add_3326(Set_Add_3326(old(pSet), second_perm->val), first_perm->val)
           && channels
             == old(channels)[first_perm->val->tid := Some_4235(snapshots[first_perm->val->tid])]
           && mem == old(mem))
         || (
          true
           && !Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), 
            Set_Add_3326(old(pSet), second_perm->val))
           && true
           && !Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), pSet)
           && snapshots
             == old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->tid := old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->tid][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet == Set_Add_3326(Set_Add_3326(old(pSet), second_perm->val), first_perm->val)
           && mem == old(mem)
           && channels == old(channels));
    return;
}



procedure Civl_CommutativityChecker_read_f_read_f_1(first_perm: One_4689, second_perm: One_4689);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3338(One_Collector_4689(first_perm), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(0)))
         == MapConst_5_3338(true)
       && MapImp_3338(One_Collector_4689(second_perm), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(1)))
         == MapConst_5_3338(true)
       && MapImp_3338(Set_Collector_4217(pSet), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(2)))
         == MapConst_5_3338(true));
  requires (forall first_k: int :: 
    true
       ==> 
      true
       ==> 
      first_k < mem[first_perm->val->mem_index]->ts
       ==> 
      Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val))
       ==> channels[first_perm->val->tid] == None_4235());
  requires (forall first_k: int :: 
    true
       ==> 
      true
       ==> 
      first_k < mem[first_perm->val->mem_index]->ts
       ==> 
      Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val))
       ==> Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val)));
  requires true
     ==> 
    Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val))
     ==> channels[first_perm->val->tid] == None_4235();
  requires true
     ==> 
    Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val))
     ==> Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val));
  requires channels[first_perm->val->tid] == None_4235();
  requires 1 <= first_perm->val->mem_index && first_perm->val->mem_index <= n;
  requires (forall second_k: int :: 
    true
       ==> 
      true
       ==> 
      second_k < mem[second_perm->val->mem_index]->ts
       ==> 
      Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), Set_Add_3326(pSet, second_perm->val))
       ==> channels[second_perm->val->tid] == None_4235());
  requires (forall second_k: int :: 
    true
       ==> 
      true
       ==> 
      second_k < mem[second_perm->val->mem_index]->ts
       ==> 
      Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), Set_Add_3326(pSet, second_perm->val))
       ==> Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), Set_Add_3326(pSet, second_perm->val)));
  requires true
     ==> 
    Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), Set_Add_3326(pSet, second_perm->val))
     ==> channels[second_perm->val->tid] == None_4235();
  requires true
     ==> 
    Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), Set_Add_3326(pSet, second_perm->val))
     ==> Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), Set_Add_3326(pSet, second_perm->val));
  requires channels[second_perm->val->tid] == None_4235();
  requires 1 <= second_perm->val->mem_index && second_perm->val->mem_index <= n;
  requires !Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val));
  modifies mem, pSet, channels, snapshots;



implementation Civl_GatePreservationChecker_read_f_read_f_1(first_perm: One_4689, second_perm: One_4689)
{

  init:
    call read_f(second_perm);
    assert (exists Civl_partition_Permission: [Permission]int :: 
        MapImp_3338(One_Collector_4689(first_perm), 
              MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(0)))
             == MapConst_5_3338(true)
           && MapImp_3338(Set_Collector_4217(pSet), 
              MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(1)))
             == MapConst_5_3338(true))
       ==> (forall first_k: int :: 
        true
           ==> 
          true
           ==> 
          first_k < mem[first_perm->val->mem_index]->ts
           ==> 
          Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val))
           ==> channels[first_perm->val->tid] == None_4235());
    assert (exists Civl_partition_Permission: [Permission]int :: 
        MapImp_3338(One_Collector_4689(first_perm), 
              MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(0)))
             == MapConst_5_3338(true)
           && MapImp_3338(Set_Collector_4217(pSet), 
              MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(1)))
             == MapConst_5_3338(true))
       ==> (forall first_k: int :: 
        true
           ==> 
          true
           ==> 
          first_k < mem[first_perm->val->mem_index]->ts
           ==> 
          Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val))
           ==> Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val)));
    assert (exists Civl_partition_Permission: [Permission]int :: 
        MapImp_3338(One_Collector_4689(first_perm), 
              MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(0)))
             == MapConst_5_3338(true)
           && MapImp_3338(Set_Collector_4217(pSet), 
              MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(1)))
             == MapConst_5_3338(true))
       ==> 
      true
       ==> 
      Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val))
       ==> channels[first_perm->val->tid] == None_4235();
    assert (exists Civl_partition_Permission: [Permission]int :: 
        MapImp_3338(One_Collector_4689(first_perm), 
              MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(0)))
             == MapConst_5_3338(true)
           && MapImp_3338(Set_Collector_4217(pSet), 
              MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(1)))
             == MapConst_5_3338(true))
       ==> 
      true
       ==> 
      Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val))
       ==> Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val));
    assert (exists Civl_partition_Permission: [Permission]int :: 
        MapImp_3338(One_Collector_4689(first_perm), 
              MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(0)))
             == MapConst_5_3338(true)
           && MapImp_3338(Set_Collector_4217(pSet), 
              MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(1)))
             == MapConst_5_3338(true))
       ==> channels[first_perm->val->tid] == None_4235();
    assert (exists Civl_partition_Permission: [Permission]int :: 
        MapImp_3338(One_Collector_4689(first_perm), 
              MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(0)))
             == MapConst_5_3338(true)
           && MapImp_3338(Set_Collector_4217(pSet), 
              MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(1)))
             == MapConst_5_3338(true))
       ==> 1 <= first_perm->val->mem_index && first_perm->val->mem_index <= n;
    return;
}



procedure Civl_GatePreservationChecker_read_f_read_f_1(first_perm: One_4689, second_perm: One_4689);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3338(One_Collector_4689(first_perm), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(0)))
         == MapConst_5_3338(true)
       && MapImp_3338(One_Collector_4689(second_perm), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(1)))
         == MapConst_5_3338(true)
       && MapImp_3338(Set_Collector_4217(pSet), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(2)))
         == MapConst_5_3338(true));
  requires (forall first_k: int :: 
    true
       ==> 
      true
       ==> 
      first_k < mem[first_perm->val->mem_index]->ts
       ==> 
      Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val))
       ==> channels[first_perm->val->tid] == None_4235());
  requires (forall first_k: int :: 
    true
       ==> 
      true
       ==> 
      first_k < mem[first_perm->val->mem_index]->ts
       ==> 
      Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val))
       ==> Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val)));
  requires true
     ==> 
    Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val))
     ==> channels[first_perm->val->tid] == None_4235();
  requires true
     ==> 
    Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val))
     ==> Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val));
  requires channels[first_perm->val->tid] == None_4235();
  requires 1 <= first_perm->val->mem_index && first_perm->val->mem_index <= n;
  requires (forall second_k: int :: 
    true
       ==> 
      true
       ==> 
      second_k < mem[second_perm->val->mem_index]->ts
       ==> 
      Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), Set_Add_3326(pSet, second_perm->val))
       ==> channels[second_perm->val->tid] == None_4235());
  requires (forall second_k: int :: 
    true
       ==> 
      true
       ==> 
      second_k < mem[second_perm->val->mem_index]->ts
       ==> 
      Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), Set_Add_3326(pSet, second_perm->val))
       ==> Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), Set_Add_3326(pSet, second_perm->val)));
  requires true
     ==> 
    Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), Set_Add_3326(pSet, second_perm->val))
     ==> channels[second_perm->val->tid] == None_4235();
  requires true
     ==> 
    Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), Set_Add_3326(pSet, second_perm->val))
     ==> Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), Set_Add_3326(pSet, second_perm->val));
  requires channels[second_perm->val->tid] == None_4235();
  requires 1 <= second_perm->val->mem_index && second_perm->val->mem_index <= n;
  requires !Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), Set_Add_3326(pSet, second_perm->val));
  modifies mem, pSet, channels, snapshots;



implementation Civl_CommutativityChecker_read_f_main_f_1(first_perm: One_4689, second_tid: Tid, second_sps: Set_4217)
   returns (second_Civl_PAs_read_f: [read_f]int)
{

  init:
    call read_f(first_perm);
    call second_Civl_PAs_read_f := main_f(second_tid, second_sps);
    assert true
       ==> (exists {:pool "K"} Civl_first_k#0: int, {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), pSet)
             && second_Civl_PAs_read_f
               == MapAdd_9189(MapConst_3_9200(0), 
                MapIte_9207_3((lambda second_pa: read_f :: 
                    1 <= second_pa->perm->val->mem_index
                       && second_pa->perm->val->mem_index <= n
                       && second_pa->perm->val->tid == second_tid), 
                  MapConst_3_9200(1), 
                  MapConst_3_9200(0)))
             && snapshots
               == old(snapshots)[first_perm->val->tid := old(snapshots)[first_perm->val->tid][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3326(old(pSet), first_perm->val)
             && channels
               == old(channels)[first_perm->val->tid := Some_4235(snapshots[first_perm->val->tid])]
             && mem == old(mem))
         || (exists {:pool "K"} Civl_first_k#0: int, {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && !Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), pSet)
             && second_Civl_PAs_read_f
               == MapAdd_9189(MapConst_3_9200(0), 
                MapIte_9207_3((lambda second_pa: read_f :: 
                    1 <= second_pa->perm->val->mem_index
                       && second_pa->perm->val->mem_index <= n
                       && second_pa->perm->val->tid == second_tid), 
                  MapConst_3_9200(1), 
                  MapConst_3_9200(0)))
             && snapshots
               == old(snapshots)[first_perm->val->tid := old(snapshots)[first_perm->val->tid][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3326(old(pSet), first_perm->val)
             && mem == old(mem)
             && channels == old(channels))
         || (
          true
           && true
           && Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), pSet)
           && second_Civl_PAs_read_f
             == MapAdd_9189(MapConst_3_9200(0), 
              MapIte_9207_3((lambda second_pa: read_f :: 
                  1 <= second_pa->perm->val->mem_index
                     && second_pa->perm->val->mem_index <= n
                     && second_pa->perm->val->tid == second_tid), 
                MapConst_3_9200(1), 
                MapConst_3_9200(0)))
           && snapshots
             == old(snapshots)[first_perm->val->tid := old(snapshots)[first_perm->val->tid][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet == Set_Add_3326(old(pSet), first_perm->val)
           && channels
             == old(channels)[first_perm->val->tid := Some_4235(snapshots[first_perm->val->tid])]
           && mem == old(mem))
         || (
          true
           && true
           && !Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), pSet)
           && second_Civl_PAs_read_f
             == MapAdd_9189(MapConst_3_9200(0), 
              MapIte_9207_3((lambda second_pa: read_f :: 
                  1 <= second_pa->perm->val->mem_index
                     && second_pa->perm->val->mem_index <= n
                     && second_pa->perm->val->tid == second_tid), 
                MapConst_3_9200(1), 
                MapConst_3_9200(0)))
           && snapshots
             == old(snapshots)[first_perm->val->tid := old(snapshots)[first_perm->val->tid][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet == Set_Add_3326(old(pSet), first_perm->val)
           && mem == old(mem)
           && channels == old(channels));
    return;
}



procedure Civl_CommutativityChecker_read_f_main_f_1(first_perm: One_4689, second_tid: Tid, second_sps: Set_4217)
   returns (second_Civl_PAs_read_f: [read_f]int);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3338(One_Collector_4689(first_perm), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(0)))
         == MapConst_5_3338(true)
       && MapImp_3338(Set_Collector_4217(second_sps), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(1)))
         == MapConst_5_3338(true)
       && MapImp_3338(Set_Collector_4217(pSet), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(2)))
         == MapConst_5_3338(true));
  requires (forall first_k: int :: 
    true
       ==> 
      true
       ==> 
      first_k < mem[first_perm->val->mem_index]->ts
       ==> 
      Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val))
       ==> channels[first_perm->val->tid] == None_4235());
  requires (forall first_k: int :: 
    true
       ==> 
      true
       ==> 
      first_k < mem[first_perm->val->mem_index]->ts
       ==> 
      Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val))
       ==> Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val)));
  requires true
     ==> 
    Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val))
     ==> channels[first_perm->val->tid] == None_4235();
  requires true
     ==> 
    Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val))
     ==> Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val));
  requires channels[first_perm->val->tid] == None_4235();
  requires 1 <= first_perm->val->mem_index && first_perm->val->mem_index <= n;
  requires true ==> channels[second_tid] == None_4235();
  requires true ==> second_sps == WholeTidPermission(second_tid);
  requires !Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val));
  modifies mem, pSet, channels, snapshots;



implementation Civl_GatePreservationChecker_main_f_read_f_1(first_tid: Tid, first_sps: Set_4217, second_perm: One_4689)
   returns (first_Civl_PAs_read_f: [read_f]int)
{

  init:
    call read_f(second_perm);
    assert (exists Civl_partition_Permission: [Permission]int :: 
        MapImp_3338(Set_Collector_4217(first_sps), 
              MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(0)))
             == MapConst_5_3338(true)
           && MapImp_3338(Set_Collector_4217(pSet), 
              MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(1)))
             == MapConst_5_3338(true))
       ==> 
      true
       ==> channels[first_tid] == None_4235();
    assert (exists Civl_partition_Permission: [Permission]int :: 
        MapImp_3338(Set_Collector_4217(first_sps), 
              MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(0)))
             == MapConst_5_3338(true)
           && MapImp_3338(Set_Collector_4217(pSet), 
              MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(1)))
             == MapConst_5_3338(true))
       ==> 
      true
       ==> first_sps == WholeTidPermission(first_tid);
    return;
}



procedure Civl_GatePreservationChecker_main_f_read_f_1(first_tid: Tid, first_sps: Set_4217, second_perm: One_4689)
   returns (first_Civl_PAs_read_f: [read_f]int);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3338(Set_Collector_4217(first_sps), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(0)))
         == MapConst_5_3338(true)
       && MapImp_3338(One_Collector_4689(second_perm), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(1)))
         == MapConst_5_3338(true)
       && MapImp_3338(Set_Collector_4217(pSet), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(2)))
         == MapConst_5_3338(true));
  requires true ==> channels[first_tid] == None_4235();
  requires true ==> first_sps == WholeTidPermission(first_tid);
  requires (forall second_k: int :: 
    true
       ==> 
      true
       ==> 
      second_k < mem[second_perm->val->mem_index]->ts
       ==> 
      Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), Set_Add_3326(pSet, second_perm->val))
       ==> channels[second_perm->val->tid] == None_4235());
  requires (forall second_k: int :: 
    true
       ==> 
      true
       ==> 
      second_k < mem[second_perm->val->mem_index]->ts
       ==> 
      Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), Set_Add_3326(pSet, second_perm->val))
       ==> Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), Set_Add_3326(pSet, second_perm->val)));
  requires true
     ==> 
    Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), Set_Add_3326(pSet, second_perm->val))
     ==> channels[second_perm->val->tid] == None_4235();
  requires true
     ==> 
    Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), Set_Add_3326(pSet, second_perm->val))
     ==> Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), Set_Add_3326(pSet, second_perm->val));
  requires channels[second_perm->val->tid] == None_4235();
  requires 1 <= second_perm->val->mem_index && second_perm->val->mem_index <= n;
  requires !Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), Set_Add_3326(pSet, second_perm->val));
  modifies mem, pSet, channels, snapshots;



implementation Civl_CommutativityChecker_main_f_read_f_1(first_tid: Tid, first_sps: Set_4217, second_perm: One_4689)
   returns (first_Civl_PAs_read_f: [read_f]int)
{

  init:
    call first_Civl_PAs_read_f := main_f(first_tid, first_sps);
    call read_f(second_perm);
    assert true
       ==> (exists {:pool "K"} Civl_second_k#0: int, {:pool "V"} Civl_second_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_v(Civl_second_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), pSet)
             && true
             && snapshots
               == old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]]
             && pSet == Set_Add_3326(old(pSet), second_perm->val)
             && channels
               == old(channels)[second_perm->val->tid := Some_4235(snapshots[second_perm->val->tid])]
             && first_Civl_PAs_read_f
               == MapAdd_9189(MapConst_3_9200(0), 
                MapIte_9207_3((lambda first_pa: read_f :: 
                    1 <= first_pa->perm->val->mem_index
                       && first_pa->perm->val->mem_index <= n
                       && first_pa->perm->val->tid == first_tid), 
                  MapConst_3_9200(1), 
                  MapConst_3_9200(0)))
             && mem == old(mem))
         || (exists {:pool "K"} Civl_second_k#0: int, {:pool "V"} Civl_second_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_v(Civl_second_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && !Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), pSet)
             && true
             && snapshots
               == old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]]
             && pSet == Set_Add_3326(old(pSet), second_perm->val)
             && first_Civl_PAs_read_f
               == MapAdd_9189(MapConst_3_9200(0), 
                MapIte_9207_3((lambda first_pa: read_f :: 
                    1 <= first_pa->perm->val->mem_index
                       && first_pa->perm->val->mem_index <= n
                       && first_pa->perm->val->tid == first_tid), 
                  MapConst_3_9200(1), 
                  MapConst_3_9200(0)))
             && channels == old(channels)
             && mem == old(mem))
         || (
          true
           && Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), pSet)
           && true
           && snapshots
             == old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := mem[second_perm->val->mem_index]]]
           && pSet == Set_Add_3326(old(pSet), second_perm->val)
           && channels
             == old(channels)[second_perm->val->tid := Some_4235(snapshots[second_perm->val->tid])]
           && first_Civl_PAs_read_f
             == MapAdd_9189(MapConst_3_9200(0), 
              MapIte_9207_3((lambda first_pa: read_f :: 
                  1 <= first_pa->perm->val->mem_index
                     && first_pa->perm->val->mem_index <= n
                     && first_pa->perm->val->tid == first_tid), 
                MapConst_3_9200(1), 
                MapConst_3_9200(0)))
           && mem == old(mem))
         || (
          true
           && !Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), pSet)
           && true
           && snapshots
             == old(snapshots)[second_perm->val->tid := old(snapshots)[second_perm->val->tid][second_perm->val->mem_index := mem[second_perm->val->mem_index]]]
           && pSet == Set_Add_3326(old(pSet), second_perm->val)
           && first_Civl_PAs_read_f
             == MapAdd_9189(MapConst_3_9200(0), 
              MapIte_9207_3((lambda first_pa: read_f :: 
                  1 <= first_pa->perm->val->mem_index
                     && first_pa->perm->val->mem_index <= n
                     && first_pa->perm->val->tid == first_tid), 
                MapConst_3_9200(1), 
                MapConst_3_9200(0)))
           && channels == old(channels)
           && mem == old(mem));
    return;
}



procedure Civl_CommutativityChecker_main_f_read_f_1(first_tid: Tid, first_sps: Set_4217, second_perm: One_4689)
   returns (first_Civl_PAs_read_f: [read_f]int);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3338(Set_Collector_4217(first_sps), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(0)))
         == MapConst_5_3338(true)
       && MapImp_3338(One_Collector_4689(second_perm), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(1)))
         == MapConst_5_3338(true)
       && MapImp_3338(Set_Collector_4217(pSet), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(2)))
         == MapConst_5_3338(true));
  requires true ==> channels[first_tid] == None_4235();
  requires true ==> first_sps == WholeTidPermission(first_tid);
  requires (forall second_k: int :: 
    true
       ==> 
      true
       ==> 
      second_k < mem[second_perm->val->mem_index]->ts
       ==> 
      Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), Set_Add_3326(pSet, second_perm->val))
       ==> channels[second_perm->val->tid] == None_4235());
  requires (forall second_k: int :: 
    true
       ==> 
      true
       ==> 
      second_k < mem[second_perm->val->mem_index]->ts
       ==> 
      Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), Set_Add_3326(pSet, second_perm->val))
       ==> Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), Set_Add_3326(pSet, second_perm->val)));
  requires true
     ==> 
    Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), Set_Add_3326(pSet, second_perm->val))
     ==> channels[second_perm->val->tid] == None_4235();
  requires true
     ==> 
    Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), Set_Add_3326(pSet, second_perm->val))
     ==> Set_IsSubset_3338(WholeTidPermission(second_perm->val->tid), Set_Add_3326(pSet, second_perm->val));
  requires channels[second_perm->val->tid] == None_4235();
  requires 1 <= second_perm->val->mem_index && second_perm->val->mem_index <= n;
  requires true;
  modifies mem, pSet, channels, snapshots;



implementation Civl_GatePreservationChecker_read_f_main_f_1(first_perm: One_4689, second_tid: Tid, second_sps: Set_4217)
   returns (second_Civl_PAs_read_f: [read_f]int)
{

  init:
    call second_Civl_PAs_read_f := main_f(second_tid, second_sps);
    assert (exists Civl_partition_Permission: [Permission]int :: 
        MapImp_3338(One_Collector_4689(first_perm), 
              MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(0)))
             == MapConst_5_3338(true)
           && MapImp_3338(Set_Collector_4217(pSet), 
              MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(1)))
             == MapConst_5_3338(true))
       ==> (forall first_k: int :: 
        true
           ==> 
          true
           ==> 
          first_k < mem[first_perm->val->mem_index]->ts
           ==> 
          Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val))
           ==> channels[first_perm->val->tid] == None_4235());
    assert (exists Civl_partition_Permission: [Permission]int :: 
        MapImp_3338(One_Collector_4689(first_perm), 
              MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(0)))
             == MapConst_5_3338(true)
           && MapImp_3338(Set_Collector_4217(pSet), 
              MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(1)))
             == MapConst_5_3338(true))
       ==> (forall first_k: int :: 
        true
           ==> 
          true
           ==> 
          first_k < mem[first_perm->val->mem_index]->ts
           ==> 
          Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val))
           ==> Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val)));
    assert (exists Civl_partition_Permission: [Permission]int :: 
        MapImp_3338(One_Collector_4689(first_perm), 
              MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(0)))
             == MapConst_5_3338(true)
           && MapImp_3338(Set_Collector_4217(pSet), 
              MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(1)))
             == MapConst_5_3338(true))
       ==> 
      true
       ==> 
      Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val))
       ==> channels[first_perm->val->tid] == None_4235();
    assert (exists Civl_partition_Permission: [Permission]int :: 
        MapImp_3338(One_Collector_4689(first_perm), 
              MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(0)))
             == MapConst_5_3338(true)
           && MapImp_3338(Set_Collector_4217(pSet), 
              MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(1)))
             == MapConst_5_3338(true))
       ==> 
      true
       ==> 
      Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val))
       ==> Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val));
    assert (exists Civl_partition_Permission: [Permission]int :: 
        MapImp_3338(One_Collector_4689(first_perm), 
              MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(0)))
             == MapConst_5_3338(true)
           && MapImp_3338(Set_Collector_4217(pSet), 
              MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(1)))
             == MapConst_5_3338(true))
       ==> channels[first_perm->val->tid] == None_4235();
    assert (exists Civl_partition_Permission: [Permission]int :: 
        MapImp_3338(One_Collector_4689(first_perm), 
              MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(0)))
             == MapConst_5_3338(true)
           && MapImp_3338(Set_Collector_4217(pSet), 
              MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(1)))
             == MapConst_5_3338(true))
       ==> 1 <= first_perm->val->mem_index && first_perm->val->mem_index <= n;
    return;
}



procedure Civl_GatePreservationChecker_read_f_main_f_1(first_perm: One_4689, second_tid: Tid, second_sps: Set_4217)
   returns (second_Civl_PAs_read_f: [read_f]int);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3338(One_Collector_4689(first_perm), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(0)))
         == MapConst_5_3338(true)
       && MapImp_3338(Set_Collector_4217(second_sps), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(1)))
         == MapConst_5_3338(true)
       && MapImp_3338(Set_Collector_4217(pSet), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(2)))
         == MapConst_5_3338(true));
  requires (forall first_k: int :: 
    true
       ==> 
      true
       ==> 
      first_k < mem[first_perm->val->mem_index]->ts
       ==> 
      Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val))
       ==> channels[first_perm->val->tid] == None_4235());
  requires (forall first_k: int :: 
    true
       ==> 
      true
       ==> 
      first_k < mem[first_perm->val->mem_index]->ts
       ==> 
      Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val))
       ==> Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val)));
  requires true
     ==> 
    Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val))
     ==> channels[first_perm->val->tid] == None_4235();
  requires true
     ==> 
    Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val))
     ==> Set_IsSubset_3338(WholeTidPermission(first_perm->val->tid), Set_Add_3326(pSet, first_perm->val));
  requires channels[first_perm->val->tid] == None_4235();
  requires 1 <= first_perm->val->mem_index && first_perm->val->mem_index <= n;
  requires true ==> channels[second_tid] == None_4235();
  requires true ==> second_sps == WholeTidPermission(second_tid);
  requires true;
  modifies mem, pSet, channels, snapshots;



implementation Civl_CommutativityChecker_main_f_main_f_1(first_tid: Tid, first_sps: Set_4217, second_tid: Tid, second_sps: Set_4217)
   returns (first_Civl_PAs_read_f: [read_f]int, second_Civl_PAs_read_f: [read_f]int)
{

  init:
    call first_Civl_PAs_read_f := main_f(first_tid, first_sps);
    call second_Civl_PAs_read_f := main_f(second_tid, second_sps);
    assert true
       ==> true
         && true
         && second_Civl_PAs_read_f
           == MapAdd_9189(MapConst_3_9200(0), 
            MapIte_9207_3((lambda second_pa: read_f :: 
                1 <= second_pa->perm->val->mem_index
                   && second_pa->perm->val->mem_index <= n
                   && second_pa->perm->val->tid == second_tid), 
              MapConst_3_9200(1), 
              MapConst_3_9200(0)))
         && first_Civl_PAs_read_f
           == MapAdd_9189(MapConst_3_9200(0), 
            MapIte_9207_3((lambda first_pa: read_f :: 
                1 <= first_pa->perm->val->mem_index
                   && first_pa->perm->val->mem_index <= n
                   && first_pa->perm->val->tid == first_tid), 
              MapConst_3_9200(1), 
              MapConst_3_9200(0)))
         && channels == old(channels)
         && pSet == old(pSet);
    return;
}



procedure Civl_CommutativityChecker_main_f_main_f_1(first_tid: Tid, first_sps: Set_4217, second_tid: Tid, second_sps: Set_4217)
   returns (first_Civl_PAs_read_f: [read_f]int, second_Civl_PAs_read_f: [read_f]int);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3338(Set_Collector_4217(first_sps), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(0)))
         == MapConst_5_3338(true)
       && MapImp_3338(Set_Collector_4217(second_sps), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(1)))
         == MapConst_5_3338(true)
       && MapImp_3338(Set_Collector_4217(pSet), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(2)))
         == MapConst_5_3338(true));
  requires true ==> channels[first_tid] == None_4235();
  requires true ==> first_sps == WholeTidPermission(first_tid);
  requires true ==> channels[second_tid] == None_4235();
  requires true ==> second_sps == WholeTidPermission(second_tid);
  requires true;
  modifies mem, pSet, channels, snapshots;



procedure Civl_PendingAsyncNoninterferenceChecker_read_f_1(perm: One_4689);
  requires (forall k: int :: 
    true
       ==> 
      true
       ==> 
      k < mem[perm->val->mem_index]->ts
       ==> 
      Set_IsSubset_3338(WholeTidPermission(perm->val->tid), Set_Add_3326(pSet, perm->val))
       ==> channels[perm->val->tid] == None_4235());
  requires (forall k: int :: 
    true
       ==> 
      true
       ==> 
      k < mem[perm->val->mem_index]->ts
       ==> 
      Set_IsSubset_3338(WholeTidPermission(perm->val->tid), Set_Add_3326(pSet, perm->val))
       ==> Set_IsSubset_3338(WholeTidPermission(perm->val->tid), Set_Add_3326(pSet, perm->val)));
  requires true
     ==> 
    Set_IsSubset_3338(WholeTidPermission(perm->val->tid), Set_Add_3326(pSet, perm->val))
     ==> channels[perm->val->tid] == None_4235();
  requires true
     ==> 
    Set_IsSubset_3338(WholeTidPermission(perm->val->tid), Set_Add_3326(pSet, perm->val))
     ==> Set_IsSubset_3338(WholeTidPermission(perm->val->tid), Set_Add_3326(pSet, perm->val));
  requires channels[perm->val->tid] == None_4235();
  requires 1 <= perm->val->mem_index && perm->val->mem_index <= n;
  modifies mem, pSet, channels, snapshots;



implementation Civl_PendingAsyncNoninterferenceChecker_read_f_1(perm: One_4689)
{
  var Civl_global_old_mem: [int]StampedValue;
  var Civl_global_old_pSet: Set_4217;
  var Civl_global_old_channels: [Tid]Option_4235;
  var Civl_global_old_snapshots: [Tid][int]StampedValue;
  var Civl_linear_Permission_available: [Permission]bool;

  init:
    Civl_global_old_mem, Civl_global_old_pSet, Civl_global_old_channels, Civl_global_old_snapshots := mem, pSet, channels, snapshots;
    Civl_linear_Permission_available := MapOr_4217(Set_Collector_4217(pSet), 
      MapOr_4217(One_Collector_4689(perm), MapConst_5_3338(false)));
    call read_f(perm);
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Permission_available, Civl_global_old_mem, Civl_global_old_pSet, Civl_global_old_channels, Civl_global_old_snapshots);
    return;
}



procedure Civl_PendingAsyncNoninterferenceChecker_main_f_1(tid: Tid, sps: Set_4217) returns (Civl_PAs_read_f: [read_f]int);
  requires true ==> channels[tid] == None_4235();
  requires true ==> sps == WholeTidPermission(tid);
  modifies mem, pSet, channels, snapshots;



implementation Civl_PendingAsyncNoninterferenceChecker_main_f_1(tid: Tid, sps: Set_4217) returns (Civl_PAs_read_f: [read_f]int)
{
  var Civl_global_old_mem: [int]StampedValue;
  var Civl_global_old_pSet: Set_4217;
  var Civl_global_old_channels: [Tid]Option_4235;
  var Civl_global_old_snapshots: [Tid][int]StampedValue;
  var Civl_linear_Permission_available: [Permission]bool;

  init:
    Civl_global_old_mem, Civl_global_old_pSet, Civl_global_old_channels, Civl_global_old_snapshots := mem, pSet, channels, snapshots;
    Civl_linear_Permission_available := MapOr_4217(Set_Collector_4217(pSet), 
      MapOr_4217(Set_Collector_4217(sps), MapConst_5_3338(false)));
    call Civl_PAs_read_f := main_f(tid, sps);
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Permission_available, Civl_global_old_mem, Civl_global_old_pSet, Civl_global_old_channels, Civl_global_old_snapshots);
    return;
}



procedure {:inline 1} Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Permission_in: [Permission]bool, 
    Civl_global_old_mem: [int]StampedValue, 
    Civl_global_old_pSet: Set_4217, 
    Civl_global_old_channels: [Tid]Option_4235, 
    Civl_global_old_snapshots: [Tid][int]StampedValue);



implementation Civl_Wrapper_NoninterferenceChecker_1(Civl_Civl_linear_Permission_in: [Permission]bool, 
    Civl_Civl_global_old_mem: [int]StampedValue, 
    Civl_Civl_global_old_pSet: Set_4217, 
    Civl_Civl_global_old_channels: [Tid]Option_4235, 
    Civl_Civl_global_old_snapshots: [Tid][int]StampedValue)
{

  enter:
    return;
}



implementation Civl_LinearityChecker_main_f(tid: Tid, sps: Set_4217) returns (Civl_PAs_read_f: [read_f]int)
{
  var Civl_pa1_read_f: read_f;
  var Civl_pa2_read_f: read_f;

  init:
    call Civl_PAs_read_f := main_f(tid, sps);
    goto Permission_out_of_thin_air_read_f, Permission_duplication_read_f, Permission_duplication_read_f_read_f;

  Permission_out_of_thin_air_read_f:
    assume Civl_pa1_read_f is read_f && Civl_PAs_read_f[Civl_pa1_read_f] >= 1;
    assert MapImp_3338(MapOr_4217(One_Collector_4689(Civl_pa1_read_f->perm), MapConst_5_3338(false)), 
        old(MapOr_4217(Set_Collector_4217(pSet), 
          MapOr_4217(Set_Collector_4217(sps), MapConst_5_3338(false)))))
       == MapConst_5_3338(true);
    return;

  Permission_duplication_read_f:
    assume Civl_pa1_read_f is read_f && Civl_PAs_read_f[Civl_pa1_read_f] >= 1;
    assert MapAnd_4217(MapOr_4217(Set_Collector_4217(pSet), MapConst_5_3338(false)), 
        MapOr_4217(One_Collector_4689(Civl_pa1_read_f->perm), MapConst_5_3338(false)))
       == MapConst_5_3338(false);
    return;

  Permission_duplication_read_f_read_f:
    assume Civl_pa1_read_f != Civl_pa2_read_f
       && 
      Civl_pa1_read_f is read_f
       && Civl_pa2_read_f is read_f
       && 
      Civl_PAs_read_f[Civl_pa1_read_f] >= 1
       && Civl_PAs_read_f[Civl_pa2_read_f] >= 1;
    assert MapAnd_4217(MapOr_4217(One_Collector_4689(Civl_pa1_read_f->perm), MapConst_5_3338(false)), 
        MapOr_4217(One_Collector_4689(Civl_pa2_read_f->perm), MapConst_5_3338(false)))
       == MapConst_5_3338(false);
    return;
}



procedure Civl_LinearityChecker_main_f(tid: Tid, sps: Set_4217) returns (Civl_PAs_read_f: [read_f]int);
  requires true ==> channels[tid] == None_4235();
  requires true ==> sps == WholeTidPermission(tid);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3338(Set_Collector_4217(sps), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(0)))
         == MapConst_5_3338(true)
       && MapImp_3338(Set_Collector_4217(pSet), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(1)))
         == MapConst_5_3338(true));
  modifies pSet;



procedure Civl_PartitionChecker_main_f(tid: Tid, sps: Set_4217) returns (Civl_PAs_read_f: [read_f]int);
  requires true ==> channels[tid] == None_4235();
  requires true ==> sps == WholeTidPermission(tid);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3338(Set_Collector_4217(sps), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(0)))
         == MapConst_5_3338(true)
       && MapImp_3338(Set_Collector_4217(pSet), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(1)))
         == MapConst_5_3338(true));
  modifies pSet;



implementation Civl_PartitionChecker_main_f(tid: Tid, sps: Set_4217) returns (Civl_PAs_read_f: [read_f]int)
{
  var Civl_local_Civl_PAs_read_f: read_f;

  Civl_PartitionChecker_main_f:
    call Civl_PAs_read_f := main_f(tid, sps);
    assert Civl_PAs_read_f != MapConst_3_9200(0) ==> true;
    goto label_Civl_PAs_read_f;

  label_Civl_PAs_read_f:
    assume Civl_PAs_read_f[Civl_local_Civl_PAs_read_f] >= 1;
    assert (forall k: int :: 
      true
         ==> 
        true
         ==> 
        k < mem[Civl_local_Civl_PAs_read_f->perm->val->mem_index]->ts
         ==> 
        Set_IsSubset_3338(WholeTidPermission(Civl_local_Civl_PAs_read_f->perm->val->tid), 
          Set_Add_3326(pSet, Civl_local_Civl_PAs_read_f->perm->val))
         ==> channels[Civl_local_Civl_PAs_read_f->perm->val->tid] == None_4235());
    assert (forall k: int :: 
      true
         ==> 
        true
         ==> 
        k < mem[Civl_local_Civl_PAs_read_f->perm->val->mem_index]->ts
         ==> 
        Set_IsSubset_3338(WholeTidPermission(Civl_local_Civl_PAs_read_f->perm->val->tid), 
          Set_Add_3326(pSet, Civl_local_Civl_PAs_read_f->perm->val))
         ==> Set_IsSubset_3338(WholeTidPermission(Civl_local_Civl_PAs_read_f->perm->val->tid), 
          Set_Add_3326(pSet, Civl_local_Civl_PAs_read_f->perm->val)));
    assert true
       ==> 
      Set_IsSubset_3338(WholeTidPermission(Civl_local_Civl_PAs_read_f->perm->val->tid), 
        Set_Add_3326(pSet, Civl_local_Civl_PAs_read_f->perm->val))
       ==> channels[Civl_local_Civl_PAs_read_f->perm->val->tid] == None_4235();
    assert true
       ==> 
      Set_IsSubset_3338(WholeTidPermission(Civl_local_Civl_PAs_read_f->perm->val->tid), 
        Set_Add_3326(pSet, Civl_local_Civl_PAs_read_f->perm->val))
       ==> Set_IsSubset_3338(WholeTidPermission(Civl_local_Civl_PAs_read_f->perm->val->tid), 
        Set_Add_3326(pSet, Civl_local_Civl_PAs_read_f->perm->val));
    assert channels[Civl_local_Civl_PAs_read_f->perm->val->tid] == None_4235();
    assert 1 <= Civl_local_Civl_PAs_read_f->perm->val->mem_index
       && Civl_local_Civl_PAs_read_f->perm->val->mem_index <= n;
    return;
}



procedure Civl_PartitionChecker_read_f(perm: One_4689);
  requires (forall k: int :: 
    true
       ==> 
      true
       ==> 
      k < mem[perm->val->mem_index]->ts
       ==> 
      Set_IsSubset_3338(WholeTidPermission(perm->val->tid), Set_Add_3326(pSet, perm->val))
       ==> channels[perm->val->tid] == None_4235());
  requires (forall k: int :: 
    true
       ==> 
      true
       ==> 
      k < mem[perm->val->mem_index]->ts
       ==> 
      Set_IsSubset_3338(WholeTidPermission(perm->val->tid), Set_Add_3326(pSet, perm->val))
       ==> Set_IsSubset_3338(WholeTidPermission(perm->val->tid), Set_Add_3326(pSet, perm->val)));
  requires true
     ==> 
    Set_IsSubset_3338(WholeTidPermission(perm->val->tid), Set_Add_3326(pSet, perm->val))
     ==> channels[perm->val->tid] == None_4235();
  requires true
     ==> 
    Set_IsSubset_3338(WholeTidPermission(perm->val->tid), Set_Add_3326(pSet, perm->val))
     ==> Set_IsSubset_3338(WholeTidPermission(perm->val->tid), Set_Add_3326(pSet, perm->val));
  requires channels[perm->val->tid] == None_4235();
  requires 1 <= perm->val->mem_index && perm->val->mem_index <= n;
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3338(One_Collector_4689(perm), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(0)))
         == MapConst_5_3338(true)
       && MapImp_3338(Set_Collector_4217(pSet), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(1)))
         == MapConst_5_3338(true));
  modifies snapshots, pSet, channels;



implementation Civl_PartitionChecker_read_f(perm: One_4689)
{

  Civl_PartitionChecker_read_f:
    call read_f(perm);
    assert false ==> true;
    return;
}



procedure Civl_ISR_base_main_f(tid: Tid, sps: Set_4217) returns (Civl_PAs_read_f: [read_f]int);
  requires (forall j: int :: 
    0 <= j && j <= n
       ==> (forall snapshots: [Tid][int]StampedValue :: 
        (forall i: int :: 
            1 <= i && i <= j
               ==> snapshots[tid][i]->ts < mem[i]->ts || snapshots[tid][i] == mem[i])
           ==> 
          true
           ==> 
          n <= j
           ==> channels[tid] == None_4235()));
  requires (forall j: int :: 
    0 <= j && j <= n
       ==> (forall snapshots: [Tid][int]StampedValue :: 
        (forall i: int :: 
            1 <= i && i <= j
               ==> snapshots[tid][i]->ts < mem[i]->ts || snapshots[tid][i] == mem[i])
           ==> 
          true
           ==> 
          n <= j
           ==> Set_IsSubset_3338(WholeTidPermission(tid), 
            Set_Union_4217(pSet, 
              Set_4217((lambda {:pool "D"} x: Permission :: 
                  x->tid == tid && 1 <= x->mem_index && x->mem_index <= j))))));
  requires (forall j: int :: 
    0 <= j && j <= n
       ==> (forall snapshots: [Tid][int]StampedValue :: 
        (forall i: int :: 
            1 <= i && i <= j
               ==> snapshots[tid][i]->ts < mem[i]->ts || snapshots[tid][i] == mem[i])
           ==> 
          true
           ==> Set_IsSubset_3338(Set_4217((lambda {:pool "D"} x: Permission :: 
                x->tid == tid && 1 <= x->mem_index && x->mem_index <= j)), 
            sps)));
  requires channels[tid] == None_4235();
  requires sps == WholeTidPermission(tid);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3338(Set_Collector_4217(sps), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(0)))
         == MapConst_5_3338(true)
       && MapImp_3338(Set_Collector_4217(pSet), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(1)))
         == MapConst_5_3338(true));
  modifies snapshots, pSet, channels;



implementation Civl_ISR_base_main_f(tid: Tid, sps: Set_4217) returns (Civl_PAs_read_f: [read_f]int)
{

  ISR_base_main_f:
    assert true ==> channels[tid] == None_4235();
    assert true ==> sps == WholeTidPermission(tid);
    call Civl_PAs_read_f := main_f(tid, sps);
    assert (exists {:pool "A"} Civl_j#0: int :: 
        0 <= Civl_j#0
           && Civl_j#0 <= n
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0
               ==> snapshots[tid][i]->ts < mem[i]->ts || snapshots[tid][i] == mem[i])
           && true
           && Civl_j#0 < n
           && true
           && pSet
             == Set_Union_4217(old(pSet), 
              Set_4217((lambda {:pool "D"} x: Permission :: 
                  x->tid == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
           && Civl_PAs_read_f
             == MapAdd_9189(MapConst_3_9200(0), 
              MapIte_9207_3((lambda {:pool "C"} pa: read_f :: 
                  Civl_j#0 + 1 <= pa->perm->val->mem_index
                     && pa->perm->val->mem_index <= n
                     && pa->perm->val->tid == tid), 
                MapConst_3_9200(1), 
                MapConst_3_9200(0)))
           && channels == old(channels))
       || (exists {:pool "A"} Civl_j#0: int :: 
        0 <= Civl_j#0
           && Civl_j#0 <= n
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0
               ==> snapshots[tid][i]->ts < mem[i]->ts || snapshots[tid][i] == mem[i])
           && true
           && n <= Civl_j#0
           && Civl_PAs_read_f == MapConst_3_9200(0)
           && pSet
             == Set_Union_4217(old(pSet), 
              Set_4217((lambda {:pool "D"} x: Permission :: 
                  x->tid == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
           && channels == old(channels)[tid := Some_4235(snapshots[tid])]);
    return;
}



procedure Civl_ISR_conclusion_main_f(tid: Tid, sps: Set_4217) returns (Civl_PAs_read_f: [read_f]int);
  requires (forall snapshot: [int]StampedValue :: 
    true
       ==> 
      (forall i: int :: 
        1 <= i && i <= n ==> snapshot[i]->ts < mem[i]->ts || snapshot[i] == mem[i])
       ==> channels[tid] == None_4235());
  requires (forall snapshot: [int]StampedValue :: 
    true
       ==> 
      (forall i: int :: 
        1 <= i && i <= n ==> snapshot[i]->ts < mem[i]->ts || snapshot[i] == mem[i])
       ==> Set_IsSubset_3338(WholeTidPermission(tid), Set_Union_4217(pSet, sps)));
  requires true ==> channels[tid] == None_4235();
  requires true ==> sps == WholeTidPermission(tid);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3338(Set_Collector_4217(sps), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(0)))
         == MapConst_5_3338(true)
       && MapImp_3338(Set_Collector_4217(pSet), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(1)))
         == MapConst_5_3338(true));
  modifies snapshots, pSet, channels;



implementation Civl_ISR_conclusion_main_f(tid: Tid, sps: Set_4217) returns (Civl_PAs_read_f: [read_f]int)
{

  ISR_conclusion_main_f:
    assert (forall j: int :: 
      0 <= j && j <= n
         ==> (forall snapshots: [Tid][int]StampedValue :: 
          (forall i: int :: 
              1 <= i && i <= j
                 ==> snapshots[tid][i]->ts < mem[i]->ts || snapshots[tid][i] == mem[i])
             ==> 
            true
             ==> 
            n <= j
             ==> channels[tid] == None_4235()));
    assert (forall j: int :: 
      0 <= j && j <= n
         ==> (forall snapshots: [Tid][int]StampedValue :: 
          (forall i: int :: 
              1 <= i && i <= j
                 ==> snapshots[tid][i]->ts < mem[i]->ts || snapshots[tid][i] == mem[i])
             ==> 
            true
             ==> 
            n <= j
             ==> Set_IsSubset_3338(WholeTidPermission(tid), 
              Set_Union_4217(pSet, 
                Set_4217((lambda {:pool "D"} x: Permission :: 
                    x->tid == tid && 1 <= x->mem_index && x->mem_index <= j))))));
    assert (forall j: int :: 
      0 <= j && j <= n
         ==> (forall snapshots: [Tid][int]StampedValue :: 
          (forall i: int :: 
              1 <= i && i <= j
                 ==> snapshots[tid][i]->ts < mem[i]->ts || snapshots[tid][i] == mem[i])
             ==> 
            true
             ==> Set_IsSubset_3338(Set_4217((lambda {:pool "D"} x: Permission :: 
                  x->tid == tid && 1 <= x->mem_index && x->mem_index <= j)), 
              sps)));
    assert channels[tid] == None_4235();
    assert sps == WholeTidPermission(tid);
    call Civl_PAs_read_f := Inv_f(tid, sps);
    assume Civl_PAs_read_f == MapConst_3_9200(0);
    assert (exists Civl_snapshot#0: [int]StampedValue :: 
      true
         && (forall i: int :: 
          1 <= i && i <= n
             ==> Civl_snapshot#0[i]->ts < mem[i]->ts || Civl_snapshot#0[i] == mem[i])
         && pSet == Set_Union_4217(old(pSet), sps)
         && channels == old(channels)[tid := Some_4235(Civl_snapshot#0)]
         && mem == old(mem));
    return;
}



procedure Civl_ISR_step_Inv_f_read_f(tid: Tid, sps: Set_4217)
   returns (Civl_PAs_read_f: [read_f]int, Civl_choice: Choice_Inv_f);
  requires (forall j: int :: 
    0 <= j && j <= n
       ==> (forall snapshots: [Tid][int]StampedValue :: 
        (forall i: int :: 
            1 <= i && i <= j
               ==> snapshots[tid][i]->ts < mem[i]->ts || snapshots[tid][i] == mem[i])
           ==> 
          true
           ==> 
          n <= j
           ==> channels[tid] == None_4235()));
  requires (forall j: int :: 
    0 <= j && j <= n
       ==> (forall snapshots: [Tid][int]StampedValue :: 
        (forall i: int :: 
            1 <= i && i <= j
               ==> snapshots[tid][i]->ts < mem[i]->ts || snapshots[tid][i] == mem[i])
           ==> 
          true
           ==> 
          n <= j
           ==> Set_IsSubset_3338(WholeTidPermission(tid), 
            Set_Union_4217(pSet, 
              Set_4217((lambda {:pool "D"} x: Permission :: 
                  x->tid == tid && 1 <= x->mem_index && x->mem_index <= j))))));
  requires (forall j: int :: 
    0 <= j && j <= n
       ==> (forall snapshots: [Tid][int]StampedValue :: 
        (forall i: int :: 
            1 <= i && i <= j
               ==> snapshots[tid][i]->ts < mem[i]->ts || snapshots[tid][i] == mem[i])
           ==> 
          true
           ==> Set_IsSubset_3338(Set_4217((lambda {:pool "D"} x: Permission :: 
                x->tid == tid && 1 <= x->mem_index && x->mem_index <= j)), 
            sps)));
  requires channels[tid] == None_4235();
  requires sps == WholeTidPermission(tid);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3338(Set_Collector_4217(sps), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(0)))
         == MapConst_5_3338(true)
       && MapImp_3338(Set_Collector_4217(pSet), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(1)))
         == MapConst_5_3338(true));
  modifies snapshots, pSet, channels;



implementation Civl_ISR_step_Inv_f_read_f(tid: Tid, sps: Set_4217)
   returns (Civl_PAs_read_f: [read_f]int, Civl_choice: Choice_Inv_f)
{

  ISR_step_Inv_f_read_f:
    call Civl_PAs_read_f, Civl_choice := Inv_f_With_Choice(tid, sps);
    assume Civl_choice is Choice_Inv_f_read_f;
    assume Civl_PAs_read_f[Civl_choice->read_f] > 0;
    Civl_PAs_read_f[Civl_choice->read_f] := Civl_PAs_read_f[Civl_choice->read_f] - 1;
    assert (forall k: int :: 
      true
         ==> 
        true
         ==> 
        k < mem[Civl_choice->read_f->perm->val->mem_index]->ts
         ==> 
        Set_IsSubset_3338(WholeTidPermission(Civl_choice->read_f->perm->val->tid), 
          Set_Add_3326(pSet, Civl_choice->read_f->perm->val))
         ==> channels[Civl_choice->read_f->perm->val->tid] == None_4235());
    assert (forall k: int :: 
      true
         ==> 
        true
         ==> 
        k < mem[Civl_choice->read_f->perm->val->mem_index]->ts
         ==> 
        Set_IsSubset_3338(WholeTidPermission(Civl_choice->read_f->perm->val->tid), 
          Set_Add_3326(pSet, Civl_choice->read_f->perm->val))
         ==> Set_IsSubset_3338(WholeTidPermission(Civl_choice->read_f->perm->val->tid), 
          Set_Add_3326(pSet, Civl_choice->read_f->perm->val)));
    assert true
       ==> 
      Set_IsSubset_3338(WholeTidPermission(Civl_choice->read_f->perm->val->tid), 
        Set_Add_3326(pSet, Civl_choice->read_f->perm->val))
       ==> channels[Civl_choice->read_f->perm->val->tid] == None_4235();
    assert true
       ==> 
      Set_IsSubset_3338(WholeTidPermission(Civl_choice->read_f->perm->val->tid), 
        Set_Add_3326(pSet, Civl_choice->read_f->perm->val))
       ==> Set_IsSubset_3338(WholeTidPermission(Civl_choice->read_f->perm->val->tid), 
        Set_Add_3326(pSet, Civl_choice->read_f->perm->val));
    assert channels[Civl_choice->read_f->perm->val->tid] == None_4235();
    assert 1 <= Civl_choice->read_f->perm->val->mem_index
       && Civl_choice->read_f->perm->val->mem_index <= n;
    call read_f(Civl_choice->read_f->perm);
    assert (exists {:pool "A"} Civl_j#0: int :: 
        0 <= Civl_j#0
           && Civl_j#0 <= n
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0
               ==> snapshots[tid][i]->ts < mem[i]->ts || snapshots[tid][i] == mem[i])
           && true
           && Civl_j#0 < n
           && true
           && pSet
             == Set_Union_4217(old(pSet), 
              Set_4217((lambda {:pool "D"} x: Permission :: 
                  x->tid == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
           && Civl_PAs_read_f
             == MapAdd_9189(MapConst_3_9200(0), 
              MapIte_9207_3((lambda {:pool "C"} pa: read_f :: 
                  Civl_j#0 + 1 <= pa->perm->val->mem_index
                     && pa->perm->val->mem_index <= n
                     && pa->perm->val->tid == tid), 
                MapConst_3_9200(1), 
                MapConst_3_9200(0)))
           && channels == old(channels))
       || (exists {:pool "A"} Civl_j#0: int :: 
        0 <= Civl_j#0
           && Civl_j#0 <= n
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0
               ==> snapshots[tid][i]->ts < mem[i]->ts || snapshots[tid][i] == mem[i])
           && true
           && n <= Civl_j#0
           && Civl_PAs_read_f == MapConst_3_9200(0)
           && pSet
             == Set_Union_4217(old(pSet), 
              Set_4217((lambda {:pool "D"} x: Permission :: 
                  x->tid == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
           && channels == old(channels)[tid := Some_4235(snapshots[tid])]);
    return;
}



procedure Civl_ISR_SideCondition_main_f(tid: Tid, sps: Set_4217) returns (Civl_PAs_read_f: [read_f]int);
  requires true ==> channels[tid] == None_4235();
  requires true ==> sps == WholeTidPermission(tid);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3338(Set_Collector_4217(sps), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(0)))
         == MapConst_5_3338(true)
       && MapImp_3338(Set_Collector_4217(pSet), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(1)))
         == MapConst_5_3338(true));
  modifies pSet;



implementation Civl_ISR_SideCondition_main_f(tid: Tid, sps: Set_4217) returns (Civl_PAs_read_f: [read_f]int)
{

  init:
    call Civl_PAs_read_f := main_f(tid, sps);
    goto Permission_only_put_perm_main_f;

  Permission_only_put_perm_main_f:
    assume true;
    assert MapImp_3338(old(MapOr_4217(Set_Collector_4217(pSet), MapConst_5_3338(false))), 
        MapOr_4217(Set_Collector_4217(pSet), MapConst_5_3338(false)))
       == MapConst_5_3338(true);
    return;
}



procedure Civl_ISR_AllPendingAsyncsInElim_read_f(perm: One_4689);
  modifies snapshots, pSet, channels;



implementation Civl_ISR_AllPendingAsyncsInElim_read_f(perm: One_4689)
{

  ISR_AllPendingAsyncsInElim_read_f:
    assume !Set_IsSubset_3338(WholeTidPermission(perm->val->tid), Set_Add_3326(pSet, perm->val));
    call read_f(perm);
    assert true;
    return;
}



procedure Civl_ISR_AllPendingAsyncsNotInElim_read_f(perm: One_4689);
  modifies snapshots, pSet, channels;



implementation Civl_ISR_AllPendingAsyncsNotInElim_read_f(perm: One_4689)
{

  ISR_AllPendingAsyncsNotInElim_read_f:
    assume Set_IsSubset_3338(WholeTidPermission(perm->val->tid), Set_Add_3326(pSet, perm->val));
    call read_f(perm);
    assert true;
    return;
}



procedure Civl_ISR_SideCondition_read_f(perm: One_4689);
  requires (forall k: int :: 
    true
       ==> 
      true
       ==> 
      k < mem[perm->val->mem_index]->ts
       ==> 
      Set_IsSubset_3338(WholeTidPermission(perm->val->tid), Set_Add_3326(pSet, perm->val))
       ==> channels[perm->val->tid] == None_4235());
  requires (forall k: int :: 
    true
       ==> 
      true
       ==> 
      k < mem[perm->val->mem_index]->ts
       ==> 
      Set_IsSubset_3338(WholeTidPermission(perm->val->tid), Set_Add_3326(pSet, perm->val))
       ==> Set_IsSubset_3338(WholeTidPermission(perm->val->tid), Set_Add_3326(pSet, perm->val)));
  requires true
     ==> 
    Set_IsSubset_3338(WholeTidPermission(perm->val->tid), Set_Add_3326(pSet, perm->val))
     ==> channels[perm->val->tid] == None_4235();
  requires true
     ==> 
    Set_IsSubset_3338(WholeTidPermission(perm->val->tid), Set_Add_3326(pSet, perm->val))
     ==> Set_IsSubset_3338(WholeTidPermission(perm->val->tid), Set_Add_3326(pSet, perm->val));
  requires channels[perm->val->tid] == None_4235();
  requires 1 <= perm->val->mem_index && perm->val->mem_index <= n;
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3338(One_Collector_4689(perm), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(0)))
         == MapConst_5_3338(true)
       && MapImp_3338(Set_Collector_4217(pSet), 
          MapEq_4217_3(Civl_partition_Permission, MapConst_3_4217(1)))
         == MapConst_5_3338(true));
  modifies snapshots, pSet, channels;



implementation Civl_ISR_SideCondition_read_f(perm: One_4689)
{

  init:
    call read_f(perm);
    goto Permission_only_put_perm_read_f;

  Permission_only_put_perm_read_f:
    assume true;
    assert MapImp_3338(old(MapOr_4217(Set_Collector_4217(pSet), MapConst_5_3338(false))), 
        MapOr_4217(Set_Collector_4217(pSet), MapConst_5_3338(false)))
       == MapConst_5_3338(true);
    return;
}



procedure Civl_ISR_InconsistencyChecker_main_f_read_f_read_f();
  modifies snapshots, pSet, channels;



implementation Civl_ISR_InconsistencyChecker_main_f_read_f_read_f()
{
  var Civl_E1_read_f: read_f;
  var Civl_E2_read_f: read_f;
  var Civl_tempg_mem: [int]StampedValue;
  var Civl_tempg_pSet: Set_4217;
  var Civl_tempg_channels: [Tid]Option_4235;
  var Civl_tempg_snapshots: [Tid][int]StampedValue;
  var Civl_templ_tid: Tid;
  var Civl_templ_sps: Set_4217;

  ISR_InconsistencyChecker_main_f_read_f_read_f:
    assume (true ==> Civl_tempg_channels[Civl_templ_tid] == None_4235())
       && (true ==> Civl_templ_sps == WholeTidPermission(Civl_templ_tid))
       && true;
    assume MapAnd_4217(MapOr_4217(Set_Collector_4217(pSet), MapConst_5_3338(false)), 
          MapOr_4217(One_Collector_4689(Civl_E1_read_f->perm), MapConst_5_3338(false)))
         == MapConst_5_3338(false)
       && MapAnd_4217(MapOr_4217(Set_Collector_4217(pSet), MapConst_5_3338(false)), 
          MapOr_4217(One_Collector_4689(Civl_E2_read_f->perm), MapConst_5_3338(false)))
         == MapConst_5_3338(false)
       && MapAnd_4217(MapOr_4217(One_Collector_4689(Civl_E1_read_f->perm), MapConst_5_3338(false)), 
          MapOr_4217(One_Collector_4689(Civl_E2_read_f->perm), MapConst_5_3338(false)))
         == MapConst_5_3338(false);
    assume MapImp_3338(MapOr_4217(One_Collector_4689(Civl_E1_read_f->perm), MapConst_5_3338(false)), 
          MapOr_4217(Set_Collector_4217(Civl_templ_sps), MapConst_5_3338(false)))
         == MapConst_5_3338(true)
       && MapImp_3338(MapOr_4217(One_Collector_4689(Civl_E2_read_f->perm), MapConst_5_3338(false)), 
          MapOr_4217(Set_Collector_4217(Civl_templ_sps), MapConst_5_3338(false)))
         == MapConst_5_3338(true);
    assert !(
      (forall k: int :: 
        true
           ==> 
          true
           ==> 
          k < mem[Civl_E1_read_f->perm->val->mem_index]->ts
           ==> 
          Set_IsSubset_3338(WholeTidPermission(Civl_E1_read_f->perm->val->tid), 
            Set_Add_3326(pSet, Civl_E1_read_f->perm->val))
           ==> channels[Civl_E1_read_f->perm->val->tid] == None_4235())
       && (forall k: int :: 
        true
           ==> 
          true
           ==> 
          k < mem[Civl_E1_read_f->perm->val->mem_index]->ts
           ==> 
          Set_IsSubset_3338(WholeTidPermission(Civl_E1_read_f->perm->val->tid), 
            Set_Add_3326(pSet, Civl_E1_read_f->perm->val))
           ==> Set_IsSubset_3338(WholeTidPermission(Civl_E1_read_f->perm->val->tid), 
            Set_Add_3326(pSet, Civl_E1_read_f->perm->val)))
       && (true
         ==> 
        Set_IsSubset_3338(WholeTidPermission(Civl_E1_read_f->perm->val->tid), 
          Set_Add_3326(pSet, Civl_E1_read_f->perm->val))
         ==> channels[Civl_E1_read_f->perm->val->tid] == None_4235())
       && (true
         ==> 
        Set_IsSubset_3338(WholeTidPermission(Civl_E1_read_f->perm->val->tid), 
          Set_Add_3326(pSet, Civl_E1_read_f->perm->val))
         ==> Set_IsSubset_3338(WholeTidPermission(Civl_E1_read_f->perm->val->tid), 
          Set_Add_3326(pSet, Civl_E1_read_f->perm->val)))
       && channels[Civl_E1_read_f->perm->val->tid] == None_4235()
       && 
      1 <= Civl_E1_read_f->perm->val->mem_index
       && Civl_E1_read_f->perm->val->mem_index <= n
       && 
      Set_IsSubset_3338(WholeTidPermission(Civl_E2_read_f->perm->val->tid), 
        Set_Add_3326(pSet, Civl_E2_read_f->perm->val))
       && 
      (forall k: int :: 
        true
           ==> 
          true
           ==> 
          k < mem[Civl_E2_read_f->perm->val->mem_index]->ts
           ==> 
          Set_IsSubset_3338(WholeTidPermission(Civl_E2_read_f->perm->val->tid), 
            Set_Add_3326(pSet, Civl_E2_read_f->perm->val))
           ==> channels[Civl_E2_read_f->perm->val->tid] == None_4235())
       && (forall k: int :: 
        true
           ==> 
          true
           ==> 
          k < mem[Civl_E2_read_f->perm->val->mem_index]->ts
           ==> 
          Set_IsSubset_3338(WholeTidPermission(Civl_E2_read_f->perm->val->tid), 
            Set_Add_3326(pSet, Civl_E2_read_f->perm->val))
           ==> Set_IsSubset_3338(WholeTidPermission(Civl_E2_read_f->perm->val->tid), 
            Set_Add_3326(pSet, Civl_E2_read_f->perm->val)))
       && (true
         ==> 
        Set_IsSubset_3338(WholeTidPermission(Civl_E2_read_f->perm->val->tid), 
          Set_Add_3326(pSet, Civl_E2_read_f->perm->val))
         ==> channels[Civl_E2_read_f->perm->val->tid] == None_4235())
       && (true
         ==> 
        Set_IsSubset_3338(WholeTidPermission(Civl_E2_read_f->perm->val->tid), 
          Set_Add_3326(pSet, Civl_E2_read_f->perm->val))
         ==> Set_IsSubset_3338(WholeTidPermission(Civl_E2_read_f->perm->val->tid), 
          Set_Add_3326(pSet, Civl_E2_read_f->perm->val)))
       && channels[Civl_E2_read_f->perm->val->tid] == None_4235()
       && 
      1 <= Civl_E2_read_f->perm->val->mem_index
       && Civl_E2_read_f->perm->val->mem_index <= n);
    return;
}


