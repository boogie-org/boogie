// Boogie program verifier version 3.1.6.0, Copyright (c) 2003-2014, Microsoft.
// Command Line Options: snapshot-scatter-gather-full2.bpl /civlDesugaredFile:blah.bpl

type Value;

type Tid;

datatype StampedValue {
  StampedValue(ts: int, value: Value)
}

datatype Permission {
  Permission(t_id: Tid, mem_index: int)
}

const n: int;

var mem: [int]StampedValue;

var r1: [Tid][int]StampedValue;

var r2: [Tid][int]StampedValue;

var pSet: Set_4272;

function {:inline} WholeTidPermission(tid: Tid) : Set_4272
{
  Set_4272((lambda {:pool "TidPermission"} x: Permission :: 
      x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n))
}

datatype main_f {
  main_f(tid: Tid, sps: Set_4272)
}

datatype read_f {
  read_f(perm: One_4565)
}

datatype main_s {
  main_s(tid: Tid)
}

const Identity: [int]int;

function {:inline} AtLeast(x: int) : [int]bool
{
  MapLe_1299(MapConst_1316_1299(x), Identity)
}

function {:inline} Range(from: int, n: int) : [int]bool
{
  MapDiff_1319(AtLeast(from), AtLeast(from + n))
}

type {:builtin "Seq"} Seq _;

pure procedure Assume(b: bool);
  ensures b;



datatype Set_4272 {
  Set_4272(val: [Permission]bool)
}

pure procedure Set_Get_3376(path: Set_4272, k: [Permission]bool) returns (l: Set_4272);



procedure create_async_3347(PA: main_f);



datatype One_4565 {
  One_4565(val: Permission)
}

procedure create_asyncs_3398(PAs: [read_f]bool);



pure procedure Set_Put_3376(path: Set_4272, l: Set_4272);



procedure create_async_3352(PA: main_s);



function {:inline} Set_IsSubset_3379(a: Set_4272, b: Set_4272) : bool
{
  IsSubset_3379(a->val, b->val)
}

function {:inline} IsSubset_3379(a: [Permission]bool, b: [Permission]bool) : bool
{
  MapImp_3379(a, b) == MapConst_5_3379(true)
}

function {:builtin "MapImp"} MapImp_3379([Permission]bool, [Permission]bool) : [Permission]bool;

function {:builtin "MapConst"} MapConst_5_3379(bool) : [Permission]bool;

pure procedure One_Put_3376(path: Set_4272, l: One_4565);



procedure set_choice_3438(choice: read_f);



function {:builtin "MapConst"} MapConst_1316_1299(int) : [int]int;

function {:builtin "MapLe"} MapLe_1299([int]int, [int]int) : [int]bool;

function {:inline} MapDiff_1319(a: [int]bool, b: [int]bool) : [int]bool
{
  MapAnd_1319(a, MapNot_1319(b))
}

function {:builtin "MapNot"} MapNot_1319([int]bool) : [int]bool;

function {:builtin "MapAnd"} MapAnd_1319([int]bool, [int]bool) : [int]bool;

datatype Vec_5 {
  Vec_5(contents: [int]bool, len: int)
}

function Default_5() : bool;

function {:builtin "MapConst"} MapConst_5_1340(bool) : [int]bool;

function {:builtin "MapIte"} MapIte_1340_5([int]bool, [int]bool, [int]bool) : [int]bool;

datatype Vec_1316 {
  Vec_1316(contents: [int]int, len: int)
}

function Default_1316() : int;

function {:builtin "MapIte"} MapIte_1340_1316([int]bool, [int]int, [int]int) : [int]int;

function {:inline} Set_Empty_4272() : Set_4272
{
  Set_4272(MapConst_5_3379(false))
}

function Set_Size_4272(a: Set_4272) : int;

function {:inline} Set_Add_4272(a: Set_4272, t: Permission) : Set_4272
{
  Set_4272(a->val[t := true])
}

function {:inline} Set_Contains_4272(a: Set_4272, t: Permission) : bool
{
  a->val[t]
}

function {:inline} Set_Remove_4272(a: Set_4272, t: Permission) : Set_4272
{
  Set_4272(a->val[t := false])
}

function {:inline} Set_Difference_4272(a: Set_4272, b: Set_4272) : Set_4272
{
  Set_4272(MapDiff_4272(a->val, b->val))
}

function {:inline} MapDiff_4272(a: [Permission]bool, b: [Permission]bool) : [Permission]bool
{
  MapAnd_4272(a, MapNot_4272(b))
}

function {:builtin "MapNot"} MapNot_4272([Permission]bool) : [Permission]bool;

function {:builtin "MapAnd"} MapAnd_4272([Permission]bool, [Permission]bool) : [Permission]bool;

function {:inline} Set_Intersection_4272(a: Set_4272, b: Set_4272) : Set_4272
{
  Set_4272(MapAnd_4272(a->val, b->val))
}

function {:inline} Set_Union_4272(a: Set_4272, b: Set_4272) : Set_4272
{
  Set_4272(MapOr_4272(a->val, b->val))
}

function {:builtin "MapOr"} MapOr_4272([Permission]bool, [Permission]bool) : [Permission]bool;

function Choice_3379(a: [Permission]bool) : Permission;

function Choice_1299(a: [int]bool) : int;

axiom n >= 1;

axiom (forall x: int :: Identity[x] == x);

axiom (forall x: Vec_1316 :: 
  { x->len } { x->contents } 
  MapIte_1340_1316(Range(0, x->len), MapConst_1316_1299(Default_1316()), x->contents)
     == MapConst_1316_1299(Default_1316()));

axiom (forall x: Vec_5 :: 
  { x->len } { x->contents } 
  MapIte_1340_5(Range(0, x->len), MapConst_5_1340(Default_5()), x->contents)
     == MapConst_5_1340(Default_5()));

axiom (forall x: Vec_1316 :: { x->len } x->len >= 0);

axiom (forall x: Vec_5 :: { x->len } x->len >= 0);

axiom (forall a: Set_4272 :: a == Set_Empty_4272() || 0 < Set_Size_4272(a));

axiom Set_Size_4272(Set_Empty_4272()) == 0;

axiom (forall a: Set_4272, t: Permission :: 
  { Set_Add_4272(a, t) } 
  Set_Size_4272(Set_Add_4272(a, t))
     == (if Set_Contains_4272(a, t) then Set_Size_4272(a) else Set_Size_4272(a) + 1));

axiom (forall a: Set_4272, t: Permission :: 
  { Set_Remove_4272(a, t) } 
  Set_Size_4272(Set_Remove_4272(a, t))
     == (if Set_Contains_4272(a, t) then Set_Size_4272(a) - 1 else Set_Size_4272(a)));

axiom (forall a: Set_4272, b: Set_4272 :: 
  { Set_Difference_4272(a, b) } 
    { Set_Intersection_4272(a, b) } 
    { Set_Union_4272(a, b) } 
  Set_Size_4272(a)
     == Set_Size_4272(Set_Difference_4272(a, b))
       + Set_Size_4272(Set_Intersection_4272(a, b)));

axiom (forall a: Set_4272, b: Set_4272 :: 
  { Set_Union_4272(a, b) } { Set_Intersection_4272(a, b) } 
  Set_Size_4272(Set_Union_4272(a, b)) + Set_Size_4272(Set_Intersection_4272(a, b))
     == Set_Size_4272(a) + Set_Size_4272(b));

axiom (forall a: [int]bool :: 
  { Choice_1299(a) } 
  a == MapConst_5_1340(false) || a[Choice_1299(a)]);

axiom (forall a: [Permission]bool :: 
  { Choice_3379(a) } 
  a == MapConst_5_3379(false) || a[Choice_3379(a)]);

function {:builtin "MapConst"} MapConst_3_4272(int) : [Permission]int;

function {:builtin "MapEq"} MapEq_4272_3([Permission]int, [Permission]int) : [Permission]bool;

function {:builtin "MapAdd"} MapAdd_4272([Permission]int, [Permission]int) : [Permission]int;

function {:builtin "MapIte"} MapIte_4272_3([Permission]bool, [Permission]int, [Permission]int) : [Permission]int;

function {:builtin "MapLe"} MapLe_4272([Permission]int, [Permission]int) : [Permission]bool;

function {:inline} Set_Collector_4272(a: Set_4272) : [Permission]bool
{
  a->val
}

function {:inline} One_Collector_4565(a: One_4565) : [Permission]bool
{
  MapOne_4565(a->val)
}

function {:inline} MapOne_4565(t: Permission) : [Permission]bool
{
  MapConst_5_3379(false)[t := true]
}

function {:inline} Collector_read_f_Permission(target: read_f) : [Permission]bool
{
  (if target is read_f
     then MapOr_4272(One_Collector_4565(target->perm), MapConst_5_3379(false))
     else MapConst_5_3379(false))
}

function {:inline} Collector_main_f_Permission(target: main_f) : [Permission]bool
{
  (if target is main_f
     then MapOr_4272(Set_Collector_4272(target->sps), MapConst_5_3379(false))
     else MapConst_5_3379(false))
}

function {:builtin "MapAdd"} MapAdd_8537([main_f]int, [main_f]int) : [main_f]int;

function {:builtin "MapConst"} MapConst_3_8548(int) : [main_f]int;

function {:builtin "MapIte"} MapIte_8555_3([main_f]bool, [main_f]int, [main_f]int) : [main_f]int;

function {:builtin "MapAdd"} MapAdd_8569([read_f]int, [read_f]int) : [read_f]int;

function {:builtin "MapConst"} MapConst_3_8580(int) : [read_f]int;

function {:builtin "MapIte"} MapIte_8587_3([read_f]bool, [read_f]int, [read_f]int) : [read_f]int;

function {:builtin "MapAdd"} MapAdd_8601([main_s]int, [main_s]int) : [main_s]int;

function {:builtin "MapConst"} MapConst_3_8612(int) : [main_s]int;

function {:builtin "MapIte"} MapIte_8619_3([main_s]bool, [main_s]int, [main_s]int) : [main_s]int;

datatype Choice_Inv_f {
  Choice_Inv_f_read_f(read_f: read_f),
  Choice_Inv_f_main_s(main_s: main_s)
}

function Trigger_start_sps(sps: Set_4272) : bool;

function Trigger_main_f'_sps2(sps2: Set_4272) : bool;

function Trigger_main_f'_done_set(done_set: Set_4272) : bool;

function Trigger_read_f_k(k: int) : bool;

function Trigger_read_f_v(v: Value) : bool;

function Trigger_write_x(x: StampedValue) : bool;

function Trigger_Inv_f_j(j: int) : bool;

function Trigger_Inv_f_sps2(sps2: Set_4272) : bool;

function Trigger_Inv_f_done_set(done_set: Set_4272) : bool;

function Trigger_Inv_f_choice(choice: read_f) : bool;

implementation start(tid: Tid) returns (Civl_PAs_main_f: [main_f]int)
{
  var sps: Set_4272;

  /*** structured program:
    call sps := Set_Get_3376(pSet, (lambda x: Permission :: 
      x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
    call create_async_3347(main_f(tid, sps));
  **** end structured program */

  anon0:
    Civl_PAs_main_f := MapConst_3_8548(0);
    sps := Set_4272((lambda x: Permission :: 
        x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
    pSet := Set_Difference_4272(pSet, sps);
    Civl_PAs_main_f := MapAdd_8537(Civl_PAs_main_f, MapConst_3_8548(0)[main_f(tid, sps) := 1]);
    return;
}



procedure {:inline 1} start(tid: Tid) returns (Civl_PAs_main_f: [main_f]int);
  modifies pSet;



function {:inline} Civl_InputOutputRelation_start(tid: Tid, Civl_PAs_main_f: [main_f]int) : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_r1: [Tid][int]StampedValue, 
      Civl_old_r2: [Tid][int]StampedValue, 
      Civl_old_pSet: Set_4272, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4272 :: 
    Set_IsSubset_3379(Set_4272((lambda x: Permission :: 
            x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n)), 
        Civl_old_pSet)
       && 
      Civl_pSet
         == Set_Difference_4272(Civl_old_pSet, 
          Set_4272((lambda x: Permission :: 
              x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n)))
       && Civl_PAs_main_f
         == MapAdd_8537(MapConst_3_8548(0), 
          MapConst_3_8548(0)[main_f(tid, 
            Set_4272((lambda x: Permission :: 
                x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n))) := 1]))
}

implementation main_f'(tid: Tid, sps: Set_4272) returns (Civl_PAs_main_s: [main_s]int)
{
  var sps2: Set_4272;
  var done_set: Set_4272;

  /*** structured program:
    sps2 := sps;
    assume {:add_to_pool "A", 0, n} true;
    assert sps
       == Set_4272((lambda x: Permission :: 
          x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
    havoc r1;
    assume (forall i: int :: 
      1 <= i && i <= n ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i]);
    call done_set := Set_Get_3376(sps2, (lambda x: Permission :: 
      x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
    call Set_Put_3376(pSet, done_set);
    call create_async_3352(main_s(tid));
  **** end structured program */

  anon0:
    Civl_PAs_main_s := MapConst_3_8612(0);
    sps2 := sps;
    assume {:add_to_pool "A", 0, n} true;
    havoc r1;
    assume (forall i: int :: 
      1 <= i && i <= n ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i]);
    done_set := Set_4272((lambda x: Permission :: 
        x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
    sps2 := Set_Difference_4272(sps2, done_set);
    pSet := Set_Union_4272(pSet, done_set);
    Civl_PAs_main_s := MapAdd_8601(Civl_PAs_main_s, MapConst_3_8612(0)[main_s(tid) := 1]);
    return;
}



procedure {:inline 1} main_f'(tid: Tid, sps: Set_4272) returns (Civl_PAs_main_s: [main_s]int);
  modifies r1, pSet;



function {:inline} Civl_InputOutputRelation_main_f'(tid: Tid, sps: Set_4272, Civl_PAs_main_s: [main_s]int) : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_r1: [Tid][int]StampedValue, 
      Civl_old_r2: [Tid][int]StampedValue, 
      Civl_old_pSet: Set_4272, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4272 :: 
    (true
         ==> (forall r1: [Tid][int]StampedValue :: 
          (forall i: int :: 
              1 <= i && i <= n
                 ==> r1[tid][i]->ts < Civl_old_mem[i]->ts || r1[tid][i] == Civl_old_mem[i])
             ==> Set_IsSubset_3379(Set_4272((lambda x: Permission :: 
                  x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n)), 
              sps)))
       && (true
         ==> sps
           == Set_4272((lambda x: Permission :: 
              x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n)))
       && 
      true
       && (forall i: int :: 
        1 <= i && i <= n
           ==> Civl_r1[tid][i]->ts < Civl_mem[i]->ts || Civl_r1[tid][i] == Civl_mem[i])
       && Civl_pSet
         == Set_Union_4272(Civl_old_pSet, 
          Set_4272((lambda x: Permission :: 
              x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n)))
       && Civl_PAs_main_s
         == MapAdd_8601(MapConst_3_8612(0), MapConst_3_8612(0)[main_s(tid) := 1]))
}

implementation read_f(perm: One_4565)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int)
{
  var {:pool "K"} k: int;
  var {:pool "V"} v: Value;

  /*** structured program:
    assume {:add_to_pool "A", 0, n} true;
    assume {:exit_condition Set_IsSubset_3379(WholeTidPermission(perm->val->t_id), pSet)} true;
    if (*)
    {
        assume {:add_to_pool "K", mem[perm->val->mem_index]->ts, k} {:add_to_pool "V", mem[perm->val->mem_index]->value, v} true;
        assume k < mem[perm->val->mem_index]->ts;
        r1[perm->val->t_id][perm->val->mem_index] := StampedValue(k, v);
    }
    else
    {
        r1[perm->val->t_id][perm->val->mem_index] := mem[perm->val->mem_index];
    }

    call One_Put_3376(pSet, perm);
    if (Set_IsSubset(WholeTidPermission(perm->val->t_id), pSet))
    {
        call create_async(main_s(perm->val->t_id));
    }
  **** end structured program */

  anon0:
    assume Trigger_read_f_v(v);
    assume Trigger_read_f_k(k);
    Civl_PAs_read_f, Civl_PAs_main_s := MapConst_3_8580(0), MapConst_3_8612(0);
    assume {:add_to_pool "A", 0, n} true;
    assume {:exit_condition Set_IsSubset_3379(WholeTidPermission(perm->val->t_id), pSet)} true;
    goto anon5_Then, anon5_Else;

  anon5_Else:
    r1[perm->val->t_id][perm->val->mem_index] := mem[perm->val->mem_index];
    goto anon3;

  anon3:
    pSet := Set_Add_4272(pSet, perm->val);
    goto anon6_Then, anon6_Else;

  anon6_Else:
    assume false;
    assume {:partition} !Set_IsSubset_3379(WholeTidPermission(perm->val->t_id), pSet);
    return;

  anon6_Then:
    assume {:partition} Set_IsSubset_3379(WholeTidPermission(perm->val->t_id), pSet);
    Civl_PAs_main_s := MapAdd_8601(Civl_PAs_main_s, MapConst_3_8612(0)[main_s(perm->val->t_id) := 1]);
    return;

  anon5_Then:
    assume false;
    assume {:add_to_pool "K", mem[perm->val->mem_index]->ts, k} {:add_to_pool "V", mem[perm->val->mem_index]->value, v} true;
    assume k < mem[perm->val->mem_index]->ts;
    r1[perm->val->t_id][perm->val->mem_index] := StampedValue(k, v);
    goto anon3;
}



procedure {:inline 1} read_f(perm: One_4565)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int);
  modifies r1, pSet;



function {:inline} Civl_InputOutputRelation_read_f(perm: One_4565, Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int)
   : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_r1: [Tid][int]StampedValue, 
      Civl_old_r2: [Tid][int]StampedValue, 
      Civl_old_pSet: Set_4272, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4272 :: 
    (exists {:pool "K"} Civl_k#0: int, {:pool "V"} Civl_v#0: Value :: 
        true
           && true
           && true
           && Civl_k#0 < Civl_mem[perm->val->mem_index]->ts
           && Set_IsSubset_3379(WholeTidPermission(perm->val->t_id), Civl_pSet)
           && Civl_PAs_read_f == MapConst_3_8580(0)
           && Civl_r1
             == Civl_old_r1[perm->val->t_id := Civl_old_r1[perm->val->t_id][perm->val->mem_index := StampedValue(Civl_k#0, Civl_v#0)]]
           && Civl_pSet == Set_Add_4272(Civl_old_pSet, perm->val)
           && Civl_PAs_main_s
             == MapAdd_8601(MapConst_3_8612(0), MapConst_3_8612(0)[main_s(perm->val->t_id) := 1]))
       || (exists {:pool "K"} Civl_k#0: int, {:pool "V"} Civl_v#0: Value :: 
        true
           && true
           && true
           && Civl_k#0 < Civl_mem[perm->val->mem_index]->ts
           && !Set_IsSubset_3379(WholeTidPermission(perm->val->t_id), Civl_pSet)
           && Civl_PAs_read_f == MapConst_3_8580(0)
           && Civl_PAs_main_s == MapConst_3_8612(0)
           && Civl_r1
             == Civl_old_r1[perm->val->t_id := Civl_old_r1[perm->val->t_id][perm->val->mem_index := StampedValue(Civl_k#0, Civl_v#0)]]
           && Civl_pSet == Set_Add_4272(Civl_old_pSet, perm->val))
       || (
        true
         && true
         && Set_IsSubset_3379(WholeTidPermission(perm->val->t_id), Civl_pSet)
         && Civl_PAs_read_f == MapConst_3_8580(0)
         && Civl_r1
           == Civl_old_r1[perm->val->t_id := Civl_old_r1[perm->val->t_id][perm->val->mem_index := Civl_mem[perm->val->mem_index]]]
         && Civl_pSet == Set_Add_4272(Civl_old_pSet, perm->val)
         && Civl_PAs_main_s
           == MapAdd_8601(MapConst_3_8612(0), MapConst_3_8612(0)[main_s(perm->val->t_id) := 1]))
       || (
        true
         && true
         && !Set_IsSubset_3379(WholeTidPermission(perm->val->t_id), Civl_pSet)
         && Civl_PAs_read_f == MapConst_3_8580(0)
         && Civl_PAs_main_s == MapConst_3_8612(0)
         && Civl_r1
           == Civl_old_r1[perm->val->t_id := Civl_old_r1[perm->val->t_id][perm->val->mem_index := Civl_mem[perm->val->mem_index]]]
         && Civl_pSet == Set_Add_4272(Civl_old_pSet, perm->val)))
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
      Civl_old_r1: [Tid][int]StampedValue, 
      Civl_old_r2: [Tid][int]StampedValue, 
      Civl_old_pSet: Set_4272, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4272 :: 
    Civl_mem == Civl_old_mem[i := StampedValue(Civl_old_mem[i]->ts + 1, v)])
}

implementation Inv_f(tid: Tid, sps: Set_4272)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int)
{
  var {:pool "A"} j: int;
  var sps2: Set_4272;
  var done_set: Set_4272;
  var choice: read_f;

  /*** structured program:
    sps2 := sps;
    assert sps
       == Set_4272((lambda x: Permission :: 
          x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
    assume {:add_to_pool "A", 0, j + 1, n} 0 <= j && j <= n;
    havoc r1;
    assume (forall i: int :: 
      1 <= i && i <= j ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i]);
    call done_set := Set_Get_3376(sps2, (lambda x: Permission :: 
      x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j));
    call Set_Put_3376(pSet, done_set);
    if (j < n)
    {
        choice := read_f(One_4565(Permission(tid, j + 1)));
        assume {:add_to_pool "C", choice} true;
        call create_asyncs((lambda {:pool "C"} pa: read_f :: 
          j + 1 <= pa->perm->val->mem_index
             && pa->perm->val->mem_index <= n
             && pa->perm->val->t_id == tid));
        call set_choice(choice);
    }
    else
    {
        call create_async(main_s(tid));
    }
  **** end structured program */

  anon0:
    assume Trigger_Inv_f_j(j);
    Civl_PAs_read_f, Civl_PAs_main_s := MapConst_3_8580(0), MapConst_3_8612(0);
    sps2 := sps;
    assume {:add_to_pool "A", 0, j + 1, n} 0 <= j && j <= n;
    havoc r1;
    assume (forall i: int :: 
      1 <= i && i <= j ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i]);
    done_set := Set_4272((lambda x: Permission :: 
        x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j));
    sps2 := Set_Difference_4272(sps2, done_set);
    pSet := Set_Union_4272(pSet, done_set);
    goto anon3_Then, anon3_Else;

  anon3_Else:
    assume {:partition} n <= j;
    Civl_PAs_main_s := MapAdd_8601(Civl_PAs_main_s, MapConst_3_8612(0)[main_s(tid) := 1]);
    return;

  anon3_Then:
    assume {:partition} j < n;
    choice := read_f(One_4565(Permission(tid, j + 1)));
    assume {:add_to_pool "C", choice} true;
    Civl_PAs_read_f := MapAdd_8569(Civl_PAs_read_f, 
      MapIte_8587_3((lambda {:pool "C"} pa: read_f :: 
          j + 1 <= pa->perm->val->mem_index
             && pa->perm->val->mem_index <= n
             && pa->perm->val->t_id == tid), 
        MapConst_3_8580(1), 
        MapConst_3_8580(0)));
    return;
}



procedure {:inline 1} Inv_f(tid: Tid, sps: Set_4272)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int);
  modifies r1, pSet;



function {:inline} Civl_InputOutputRelation_Inv_f(tid: Tid, 
    sps: Set_4272, 
    Civl_PAs_read_f: [read_f]int, 
    Civl_PAs_main_s: [main_s]int)
   : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_r1: [Tid][int]StampedValue, 
      Civl_old_r2: [Tid][int]StampedValue, 
      Civl_old_pSet: Set_4272, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4272 :: 
    (forall j: int :: 
        0 <= j && j <= n
           ==> (forall r1: [Tid][int]StampedValue :: 
            (forall i: int :: 
                1 <= i && i <= j
                   ==> r1[tid][i]->ts < Civl_old_mem[i]->ts || r1[tid][i] == Civl_old_mem[i])
               ==> Set_IsSubset_3379(Set_4272((lambda x: Permission :: 
                    x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j)), 
                sps)))
       && sps
         == Set_4272((lambda x: Permission :: 
            x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n))
       && ((exists {:pool "A"} Civl_j#0: int :: 
          0 <= Civl_j#0
             && Civl_j#0 <= n
             && (forall i: int :: 
              1 <= i && i <= Civl_j#0
                 ==> Civl_r1[tid][i]->ts < Civl_mem[i]->ts || Civl_r1[tid][i] == Civl_mem[i])
             && Civl_j#0 < n
             && true
             && Civl_PAs_main_s == MapConst_3_8612(0)
             && Civl_pSet
               == Set_Union_4272(Civl_old_pSet, 
                Set_4272((lambda x: Permission :: 
                    x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
             && Civl_PAs_read_f
               == MapAdd_8569(MapConst_3_8580(0), 
                MapIte_8587_3((lambda {:pool "C"} pa: read_f :: 
                    Civl_j#0 + 1 <= pa->perm->val->mem_index
                       && pa->perm->val->mem_index <= n
                       && pa->perm->val->t_id == tid), 
                  MapConst_3_8580(1), 
                  MapConst_3_8580(0))))
         || (exists {:pool "A"} Civl_j#0: int :: 
          0 <= Civl_j#0
             && Civl_j#0 <= n
             && (forall i: int :: 
              1 <= i && i <= Civl_j#0
                 ==> Civl_r1[tid][i]->ts < Civl_mem[i]->ts || Civl_r1[tid][i] == Civl_mem[i])
             && n <= Civl_j#0
             && Civl_PAs_read_f == MapConst_3_8580(0)
             && Civl_pSet
               == Set_Union_4272(Civl_old_pSet, 
                Set_4272((lambda x: Permission :: 
                    x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
             && Civl_PAs_main_s
               == MapAdd_8601(MapConst_3_8612(0), MapConst_3_8612(0)[main_s(tid) := 1]))))
}

implementation Inv_f_With_Choice(tid: Tid, sps: Set_4272)
   returns (Civl_PAs_read_f: [read_f]int, 
    Civl_PAs_main_s: [main_s]int, 
    Civl_choice: Choice_Inv_f)
{
  var {:pool "A"} j: int;
  var sps2: Set_4272;
  var done_set: Set_4272;
  var choice: read_f;

  /*** structured program:
    sps2 := sps;
    assert sps
       == Set_4272((lambda x: Permission :: 
          x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
    assume {:add_to_pool "A", 0, j + 1, n} 0 <= j && j <= n;
    havoc r1;
    assume (forall i: int :: 
      1 <= i && i <= j ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i]);
    call done_set := Set_Get_3376(sps2, (lambda x: Permission :: 
      x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j));
    call Set_Put_3376(pSet, done_set);
    if (j < n)
    {
        choice := read_f(One_4565(Permission(tid, j + 1)));
        assume {:add_to_pool "C", choice} true;
        call create_asyncs((lambda {:pool "C"} pa: read_f :: 
          j + 1 <= pa->perm->val->mem_index
             && pa->perm->val->mem_index <= n
             && pa->perm->val->t_id == tid));
        call set_choice(choice);
    }
    else
    {
        call create_async(main_s(tid));
    }
  **** end structured program */

  anon0:
    Civl_PAs_read_f, Civl_PAs_main_s := MapConst_3_8580(0), MapConst_3_8612(0);
    sps2 := sps;
    assert sps
       == Set_4272((lambda x: Permission :: 
          x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
    assume {:add_to_pool "A", 0, j + 1, n} 0 <= j && j <= n;
    havoc r1;
    assume (forall i: int :: 
      1 <= i && i <= j ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i]);
    done_set := Set_4272((lambda x: Permission :: 
        x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j));
    assert Set_IsSubset_3379(done_set, sps2);
    sps2 := Set_Difference_4272(sps2, done_set);
    pSet := Set_Union_4272(pSet, done_set);
    goto anon3_Then, anon3_Else;

  anon3_Else:
    assume false;
    assume {:partition} n <= j;
    Civl_PAs_main_s := MapAdd_8601(Civl_PAs_main_s, MapConst_3_8612(0)[main_s(tid) := 1]);
    return;

  anon3_Then:
    assume {:partition} j < n;
    choice := read_f(One_4565(Permission(tid, j + 1)));
    assume {:add_to_pool "C", choice} true;
    Civl_PAs_read_f := MapAdd_8569(Civl_PAs_read_f, 
      MapIte_8587_3((lambda {:pool "C"} pa: read_f :: 
          j + 1 <= pa->perm->val->mem_index
             && pa->perm->val->mem_index <= n
             && pa->perm->val->t_id == tid), 
        MapConst_3_8580(1), 
        MapConst_3_8580(0)));
    assert Civl_PAs_read_f == MapConst_3_8580(0) || Civl_PAs_read_f[choice] > 0;
    Civl_choice->read_f := choice;
    return;
}



procedure {:inline 1} Inv_f_With_Choice(tid: Tid, sps: Set_4272)
   returns (Civl_PAs_read_f: [read_f]int, 
    Civl_PAs_main_s: [main_s]int, 
    Civl_choice: Choice_Inv_f);
  modifies r1, pSet;



function {:inline} Civl_InputOutputRelation_Inv_f_With_Choice(tid: Tid, 
    sps: Set_4272, 
    Civl_PAs_read_f: [read_f]int, 
    Civl_PAs_main_s: [main_s]int, 
    Civl_choice: Choice_Inv_f)
   : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_r1: [Tid][int]StampedValue, 
      Civl_old_r2: [Tid][int]StampedValue, 
      Civl_old_pSet: Set_4272, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4272 :: 
    (forall j: int :: 
        0 <= j && j <= n
           ==> (forall r1: [Tid][int]StampedValue :: 
            (forall i: int :: 
                1 <= i && i <= j
                   ==> r1[tid][i]->ts < Civl_old_mem[i]->ts || r1[tid][i] == Civl_old_mem[i])
               ==> Set_IsSubset_3379(Set_4272((lambda x: Permission :: 
                    x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j)), 
                sps)))
       && sps
         == Set_4272((lambda x: Permission :: 
            x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n))
       && ((exists {:pool "A"} Civl_j#0: int :: 
          sps
               == Set_4272((lambda x: Permission :: 
                  x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n))
             && 0 <= Civl_j#0
             && Civl_j#0 <= n
             && (forall i: int :: 
              1 <= i && i <= Civl_j#0
                 ==> Civl_r1[tid][i]->ts < Civl_mem[i]->ts || Civl_r1[tid][i] == Civl_mem[i])
             && Set_IsSubset_3379(Set_4272((lambda x: Permission :: 
                  x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)), 
              sps)
             && Civl_j#0 < n
             && true
             && (Civl_PAs_read_f == MapConst_3_8580(0)
               || Civl_PAs_read_f[read_f(One_4565(Permission(tid, Civl_j#0 + 1)))] > 0)
             && Civl_PAs_main_s == MapConst_3_8612(0)
             && Civl_pSet
               == Set_Union_4272(Civl_old_pSet, 
                Set_4272((lambda x: Permission :: 
                    x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
             && Civl_PAs_read_f
               == MapAdd_8569(MapConst_3_8580(0), 
                MapIte_8587_3((lambda {:pool "C"} pa: read_f :: 
                    Civl_j#0 + 1 <= pa->perm->val->mem_index
                       && pa->perm->val->mem_index <= n
                       && pa->perm->val->t_id == tid), 
                  MapConst_3_8580(1), 
                  MapConst_3_8580(0)))
             && Civl_choice
               == Choice_Inv_f_read_f(read_f(One_4565(Permission(tid, Civl_j#0 + 1)))))
         || (exists {:pool "A"} Civl_j#0: int :: 
          sps
               == Set_4272((lambda x: Permission :: 
                  x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n))
             && 0 <= Civl_j#0
             && Civl_j#0 <= n
             && (forall i: int :: 
              1 <= i && i <= Civl_j#0
                 ==> Civl_r1[tid][i]->ts < Civl_mem[i]->ts || Civl_r1[tid][i] == Civl_mem[i])
             && Set_IsSubset_3379(Set_4272((lambda x: Permission :: 
                  x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)), 
              sps)
             && n <= Civl_j#0
             && Civl_PAs_read_f == MapConst_3_8580(0)
             && Civl_pSet
               == Set_Union_4272(Civl_old_pSet, 
                Set_4272((lambda x: Permission :: 
                    x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
             && Civl_PAs_main_s
               == MapAdd_8601(MapConst_3_8612(0), MapConst_3_8612(0)[main_s(tid) := 1]))))
}

implementation main_s(tid: Tid)
{
  /*** structured program:
  **** end structured program */

  anon0:
    return;
}



procedure {:inline 1} main_s(tid: Tid);



function {:inline} Civl_InputOutputRelation_main_s(tid: Tid) : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_r1: [Tid][int]StampedValue, 
      Civl_old_r2: [Tid][int]StampedValue, 
      Civl_old_pSet: Set_4272, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4272 :: 
    true)
}

implementation main_f(tid: Tid, sps: Set_4272) returns (Civl_PAs_read_f: [read_f]int)
{
  /*** structured program:
    assume {:add_to_pool "A", 0, n} true;
    assert sps
       == Set_4272((lambda x: Permission :: 
          x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
    call create_asyncs_3398((lambda pa: read_f :: 
      1 <= pa->perm->val->mem_index
         && pa->perm->val->mem_index <= n
         && pa->perm->val->t_id == tid));
  **** end structured program */

  anon0:
    Civl_PAs_read_f := MapConst_3_8580(0);
    assume {:add_to_pool "A", 0, n} true;
    Civl_PAs_read_f := MapAdd_8569(Civl_PAs_read_f, 
      MapIte_8587_3((lambda pa: read_f :: 
          1 <= pa->perm->val->mem_index
             && pa->perm->val->mem_index <= n
             && pa->perm->val->t_id == tid), 
        MapConst_3_8580(1), 
        MapConst_3_8580(0)));
    return;
}



procedure {:inline 1} main_f(tid: Tid, sps: Set_4272) returns (Civl_PAs_read_f: [read_f]int);
  modifies pSet;



function {:inline} Civl_InputOutputRelation_main_f(tid: Tid, sps: Set_4272, Civl_PAs_read_f: [read_f]int) : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_r1: [Tid][int]StampedValue, 
      Civl_old_r2: [Tid][int]StampedValue, 
      Civl_old_pSet: Set_4272, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4272 :: 
    (true
         ==> sps
           == Set_4272((lambda x: Permission :: 
              x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n)))
       && 
      true
       && Civl_PAs_read_f
         == MapAdd_8569(MapConst_3_8580(0), 
          MapIte_8587_3((lambda pa: read_f :: 
              1 <= pa->perm->val->mem_index
                 && pa->perm->val->mem_index <= n
                 && pa->perm->val->t_id == tid), 
            MapConst_3_8580(1), 
            MapConst_3_8580(0)))
       && Civl_pSet == Civl_old_pSet)
}

procedure Civl_PendingAsyncNoninterferenceChecker_read_f_1(perm: One_4565)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int);
  modifies mem, r1, r2, pSet;



implementation Civl_PendingAsyncNoninterferenceChecker_read_f_1(perm: One_4565)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int)
{
  var Civl_global_old_mem: [int]StampedValue;
  var Civl_global_old_r1: [Tid][int]StampedValue;
  var Civl_global_old_r2: [Tid][int]StampedValue;
  var Civl_global_old_pSet: Set_4272;
  var Civl_linear_Permission_available: [Permission]bool;

  init:
    Civl_global_old_mem, Civl_global_old_r1, Civl_global_old_r2, Civl_global_old_pSet := mem, r1, r2, pSet;
    Civl_linear_Permission_available := MapOr_4272(Set_Collector_4272(pSet), 
      MapOr_4272(One_Collector_4565(perm), MapConst_5_3379(false)));
    call Civl_PAs_read_f, Civl_PAs_main_s := read_f(perm);
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Permission_available, Civl_global_old_mem, Civl_global_old_r1, Civl_global_old_r2, Civl_global_old_pSet);
    return;
}



procedure Civl_PendingAsyncNoninterferenceChecker_main_s_1(tid: Tid);
  modifies mem, r1, r2, pSet;



implementation Civl_PendingAsyncNoninterferenceChecker_main_s_1(tid: Tid)
{
  var Civl_global_old_mem: [int]StampedValue;
  var Civl_global_old_r1: [Tid][int]StampedValue;
  var Civl_global_old_r2: [Tid][int]StampedValue;
  var Civl_global_old_pSet: Set_4272;
  var Civl_linear_Permission_available: [Permission]bool;

  init:
    Civl_global_old_mem, Civl_global_old_r1, Civl_global_old_r2, Civl_global_old_pSet := mem, r1, r2, pSet;
    Civl_linear_Permission_available := MapOr_4272(Set_Collector_4272(pSet), MapConst_5_3379(false));
    call main_s(tid);
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Permission_available, Civl_global_old_mem, Civl_global_old_r1, Civl_global_old_r2, Civl_global_old_pSet);
    return;
}



procedure Civl_PendingAsyncNoninterferenceChecker_main_f_1(tid: Tid, sps: Set_4272) returns (Civl_PAs_read_f: [read_f]int);
  requires true
     ==> sps
       == Set_4272((lambda x: Permission :: 
          x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
  modifies mem, r1, r2, pSet;



implementation Civl_PendingAsyncNoninterferenceChecker_main_f_1(tid: Tid, sps: Set_4272) returns (Civl_PAs_read_f: [read_f]int)
{
  var Civl_global_old_mem: [int]StampedValue;
  var Civl_global_old_r1: [Tid][int]StampedValue;
  var Civl_global_old_r2: [Tid][int]StampedValue;
  var Civl_global_old_pSet: Set_4272;
  var Civl_linear_Permission_available: [Permission]bool;

  init:
    Civl_global_old_mem, Civl_global_old_r1, Civl_global_old_r2, Civl_global_old_pSet := mem, r1, r2, pSet;
    Civl_linear_Permission_available := MapOr_4272(Set_Collector_4272(pSet), 
      MapOr_4272(Set_Collector_4272(sps), MapConst_5_3379(false)));
    call Civl_PAs_read_f := main_f(tid, sps);
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Permission_available, Civl_global_old_mem, Civl_global_old_r1, Civl_global_old_r2, Civl_global_old_pSet);
    return;
}



procedure {:inline 1} Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Permission_in: [Permission]bool, 
    Civl_global_old_mem: [int]StampedValue, 
    Civl_global_old_r1: [Tid][int]StampedValue, 
    Civl_global_old_r2: [Tid][int]StampedValue, 
    Civl_global_old_pSet: Set_4272);



implementation Civl_Wrapper_NoninterferenceChecker_1(Civl_Civl_linear_Permission_in: [Permission]bool, 
    Civl_Civl_global_old_mem: [int]StampedValue, 
    Civl_Civl_global_old_r1: [Tid][int]StampedValue, 
    Civl_Civl_global_old_r2: [Tid][int]StampedValue, 
    Civl_Civl_global_old_pSet: Set_4272)
{

  enter:
    return;
}



implementation Civl_LinearityChecker_read_f(perm: One_4565)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int)
{
  var Civl_pa1_read_f: read_f;
  var Civl_pa2_read_f: read_f;
  var Civl_pa1_main_s: main_s;
  var Civl_pa2_main_s: main_s;

  init:
    call Civl_PAs_read_f, Civl_PAs_main_s := read_f(perm);
    goto Permission_out_of_thin_air_read_f, Permission_duplication_read_f, Permission_duplication_read_f_read_f;

  Permission_out_of_thin_air_read_f:
    assume Civl_pa1_read_f is read_f && Civl_PAs_read_f[Civl_pa1_read_f] >= 1;
    assert MapImp_3379(MapOr_4272(One_Collector_4565(Civl_pa1_read_f->perm), MapConst_5_3379(false)), 
        old(MapOr_4272(Set_Collector_4272(pSet), 
          MapOr_4272(One_Collector_4565(perm), MapConst_5_3379(false)))))
       == MapConst_5_3379(true);
    return;

  Permission_duplication_read_f:
    assume Civl_pa1_read_f is read_f && Civl_PAs_read_f[Civl_pa1_read_f] >= 1;
    assert MapAnd_4272(MapOr_4272(Set_Collector_4272(pSet), MapConst_5_3379(false)), 
        MapOr_4272(One_Collector_4565(Civl_pa1_read_f->perm), MapConst_5_3379(false)))
       == MapConst_5_3379(false);
    return;

  Permission_duplication_read_f_read_f:
    assume Civl_pa1_read_f != Civl_pa2_read_f
       && 
      Civl_pa1_read_f is read_f
       && Civl_pa2_read_f is read_f
       && 
      Civl_PAs_read_f[Civl_pa1_read_f] >= 1
       && Civl_PAs_read_f[Civl_pa2_read_f] >= 1;
    assert MapAnd_4272(MapOr_4272(One_Collector_4565(Civl_pa1_read_f->perm), MapConst_5_3379(false)), 
        MapOr_4272(One_Collector_4565(Civl_pa2_read_f->perm), MapConst_5_3379(false)))
       == MapConst_5_3379(false);
    return;
}



procedure Civl_LinearityChecker_read_f(perm: One_4565)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3379(One_Collector_4565(perm), 
          MapEq_4272_3(Civl_partition_Permission, MapConst_3_4272(0)))
         == MapConst_5_3379(true)
       && MapImp_3379(Set_Collector_4272(pSet), 
          MapEq_4272_3(Civl_partition_Permission, MapConst_3_4272(1)))
         == MapConst_5_3379(true));
  modifies r1, pSet;



implementation Civl_LinearityChecker_main_f(tid: Tid, sps: Set_4272) returns (Civl_PAs_read_f: [read_f]int)
{
  var Civl_pa1_read_f: read_f;
  var Civl_pa2_read_f: read_f;

  init:
    call Civl_PAs_read_f := main_f(tid, sps);
    goto Permission_out_of_thin_air_read_f, Permission_duplication_read_f, Permission_duplication_read_f_read_f;

  Permission_out_of_thin_air_read_f:
    assume Civl_pa1_read_f is read_f && Civl_PAs_read_f[Civl_pa1_read_f] >= 1;
    assert MapImp_3379(MapOr_4272(One_Collector_4565(Civl_pa1_read_f->perm), MapConst_5_3379(false)), 
        old(MapOr_4272(Set_Collector_4272(pSet), 
          MapOr_4272(Set_Collector_4272(sps), MapConst_5_3379(false)))))
       == MapConst_5_3379(true);
    return;

  Permission_duplication_read_f:
    assume Civl_pa1_read_f is read_f && Civl_PAs_read_f[Civl_pa1_read_f] >= 1;
    assert MapAnd_4272(MapOr_4272(Set_Collector_4272(pSet), MapConst_5_3379(false)), 
        MapOr_4272(One_Collector_4565(Civl_pa1_read_f->perm), MapConst_5_3379(false)))
       == MapConst_5_3379(false);
    return;

  Permission_duplication_read_f_read_f:
    assume Civl_pa1_read_f != Civl_pa2_read_f
       && 
      Civl_pa1_read_f is read_f
       && Civl_pa2_read_f is read_f
       && 
      Civl_PAs_read_f[Civl_pa1_read_f] >= 1
       && Civl_PAs_read_f[Civl_pa2_read_f] >= 1;
    assert MapAnd_4272(MapOr_4272(One_Collector_4565(Civl_pa1_read_f->perm), MapConst_5_3379(false)), 
        MapOr_4272(One_Collector_4565(Civl_pa2_read_f->perm), MapConst_5_3379(false)))
       == MapConst_5_3379(false);
    return;
}



procedure Civl_LinearityChecker_main_f(tid: Tid, sps: Set_4272) returns (Civl_PAs_read_f: [read_f]int);
  requires true
     ==> sps
       == Set_4272((lambda x: Permission :: 
          x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3379(Set_Collector_4272(sps), 
          MapEq_4272_3(Civl_partition_Permission, MapConst_3_4272(0)))
         == MapConst_5_3379(true)
       && MapImp_3379(Set_Collector_4272(pSet), 
          MapEq_4272_3(Civl_partition_Permission, MapConst_3_4272(1)))
         == MapConst_5_3379(true));
  modifies pSet;



procedure Civl_PChecker_main_f(tid: Tid, sps: Set_4272) returns (Civl_PAs_read_f: [read_f]int);
  modifies pSet;



implementation Civl_PChecker_main_f(tid: Tid, sps: Set_4272) returns (Civl_PAs_read_f: [read_f]int)
{
  var Civl_temp_read_f: read_f;

  Civl_PChecker_main_f:
    call Civl_PAs_read_f := main_f(tid, sps);
    assert Civl_PAs_read_f != MapConst_3_8580(0) ==> true;
    goto label_read_f;

  label_read_f:
    assume Civl_PAs_read_f[Civl_temp_read_f] >= 1;
    return;
}



procedure Civl_PChecker_read_f(perm: One_4565)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int);
  modifies r1, pSet;



implementation Civl_PChecker_read_f(perm: One_4565)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int)
{
  var Civl_temp_read_f: read_f;

  Civl_PChecker_read_f:
    call Civl_PAs_read_f, Civl_PAs_main_s := read_f(perm);
    assert Civl_PAs_read_f != MapConst_3_8580(0) ==> Civl_PAs_main_s == MapConst_3_8612(0);
    goto label_read_f;

  label_read_f:
    assume Civl_PAs_read_f[Civl_temp_read_f] >= 1;
    return;
}



procedure Civl_ISR_base_main_f(tid: Tid, sps: Set_4272)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int);
  requires (forall j: int :: 
    0 <= j && j <= n
       ==> (forall r1: [Tid][int]StampedValue :: 
        (forall i: int :: 
            1 <= i && i <= j ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i])
           ==> Set_IsSubset_3379(Set_4272((lambda x: Permission :: 
                x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j)), 
            sps)));
  requires sps
     == Set_4272((lambda x: Permission :: 
        x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
  modifies r1, pSet;



implementation Civl_ISR_base_main_f(tid: Tid, sps: Set_4272)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int)
{

  ISR_base_main_f:
    assert true
       ==> sps
         == Set_4272((lambda x: Permission :: 
            x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
    call Civl_PAs_read_f := main_f(tid, sps);
    Civl_PAs_main_s := MapConst_3_8612(0);
    assert (exists {:pool "A"} Civl_j#0: int :: 
        0 <= Civl_j#0
           && Civl_j#0 <= n
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0 ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i])
           && Civl_j#0 < n
           && true
           && Civl_PAs_main_s == MapConst_3_8612(0)
           && pSet
             == Set_Union_4272(old(pSet), 
              Set_4272((lambda x: Permission :: 
                  x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
           && Civl_PAs_read_f
             == MapAdd_8569(MapConst_3_8580(0), 
              MapIte_8587_3((lambda {:pool "C"} pa: read_f :: 
                  Civl_j#0 + 1 <= pa->perm->val->mem_index
                     && pa->perm->val->mem_index <= n
                     && pa->perm->val->t_id == tid), 
                MapConst_3_8580(1), 
                MapConst_3_8580(0))))
       || (exists {:pool "A"} Civl_j#0: int :: 
        0 <= Civl_j#0
           && Civl_j#0 <= n
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0 ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i])
           && n <= Civl_j#0
           && Civl_PAs_read_f == MapConst_3_8580(0)
           && pSet
             == Set_Union_4272(old(pSet), 
              Set_4272((lambda x: Permission :: 
                  x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
           && Civl_PAs_main_s
             == MapAdd_8601(MapConst_3_8612(0), MapConst_3_8612(0)[main_s(tid) := 1]));
    return;
}



procedure Civl_ISR_conclusion_main_f(tid: Tid, sps: Set_4272)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int);
  requires true
     ==> (forall r1: [Tid][int]StampedValue :: 
      (forall i: int :: 
          1 <= i && i <= n ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i])
         ==> Set_IsSubset_3379(Set_4272((lambda x: Permission :: 
              x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n)), 
          sps));
  requires true
     ==> sps
       == Set_4272((lambda x: Permission :: 
          x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
  modifies r1, pSet;



implementation Civl_ISR_conclusion_main_f(tid: Tid, sps: Set_4272)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int)
{

  ISR_conclusion_main_f:
    assert (forall j: int :: 
      0 <= j && j <= n
         ==> (forall r1: [Tid][int]StampedValue :: 
          (forall i: int :: 
              1 <= i && i <= j ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i])
             ==> Set_IsSubset_3379(Set_4272((lambda x: Permission :: 
                  x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j)), 
              sps)));
    assert sps
       == Set_4272((lambda x: Permission :: 
          x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
    call Civl_PAs_read_f, Civl_PAs_main_s := Inv_f(tid, sps);
    assume Civl_PAs_read_f == MapConst_3_8580(0);
    assert true
       && (forall i: int :: 
        1 <= i && i <= n ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i])
       && pSet
         == Set_Union_4272(old(pSet), 
          Set_4272((lambda x: Permission :: 
              x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n)))
       && Civl_PAs_main_s
         == MapAdd_8601(MapConst_3_8612(0), MapConst_3_8612(0)[main_s(tid) := 1])
       && mem == old(mem)
       && r2 == old(r2);
    return;
}



procedure Civl_ISR_SideCondition_main_f(tid: Tid, sps: Set_4272) returns (Civl_PAs_read_f: [read_f]int);
  requires true
     ==> sps
       == Set_4272((lambda x: Permission :: 
          x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3379(Set_Collector_4272(sps), 
          MapEq_4272_3(Civl_partition_Permission, MapConst_3_4272(0)))
         == MapConst_5_3379(true)
       && MapImp_3379(Set_Collector_4272(pSet), 
          MapEq_4272_3(Civl_partition_Permission, MapConst_3_4272(1)))
         == MapConst_5_3379(true));
  modifies pSet;



implementation Civl_ISR_SideCondition_main_f(tid: Tid, sps: Set_4272) returns (Civl_PAs_read_f: [read_f]int)
{

  init:
    call Civl_PAs_read_f := main_f(tid, sps);
    goto Permission_only_put_perm_main_f;

  Permission_only_put_perm_main_f:
    assume true;
    assert MapImp_3379(old(MapOr_4272(Set_Collector_4272(pSet), MapConst_5_3379(false))), 
        MapOr_4272(Set_Collector_4272(pSet), MapConst_5_3379(false)))
       == MapConst_5_3379(true);
    return;
}



procedure Civl_ISR_step_Inv_f_read_f(tid: Tid, sps: Set_4272)
   returns (Civl_PAs_read_f: [read_f]int, 
    Civl_PAs_main_s: [main_s]int, 
    Civl_choice: Choice_Inv_f);
  requires (forall j: int :: 
    0 <= j && j <= n
       ==> (forall r1: [Tid][int]StampedValue :: 
        (forall i: int :: 
            1 <= i && i <= j ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i])
           ==> Set_IsSubset_3379(Set_4272((lambda x: Permission :: 
                x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j)), 
            sps)));
  requires sps
     == Set_4272((lambda x: Permission :: 
        x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
  modifies r1, pSet;



implementation Civl_ISR_step_Inv_f_read_f(tid: Tid, sps: Set_4272)
   returns (Civl_PAs_read_f: [read_f]int, 
    Civl_PAs_main_s: [main_s]int, 
    Civl_choice: Choice_Inv_f)
{
  var Civl_newPAs_read_f: [read_f]int;
  var Civl_newPAs_main_s: [main_s]int;
  var Civl_j#0: int;
  Civl_j#0 := n;

  ISR_step_Inv_f_read_f:
    call Civl_PAs_read_f, Civl_PAs_main_s, Civl_choice := Inv_f_With_Choice(tid, sps);
    assume Civl_choice is Choice_Inv_f_read_f;
    assume Civl_PAs_read_f[Civl_choice->read_f] > 0;
    Civl_PAs_read_f[Civl_choice->read_f] := Civl_PAs_read_f[Civl_choice->read_f] - 1;
    call Civl_newPAs_read_f, Civl_newPAs_main_s := read_f(Civl_choice->read_f->perm);
    Civl_PAs_read_f, Civl_PAs_main_s := MapAdd_8569(Civl_PAs_read_f, Civl_newPAs_read_f), MapAdd_8601(Civl_PAs_main_s, Civl_newPAs_main_s);
    // assert (exists {:pool "A"} Civl_j#0: int :: 
    //     0 <= Civl_j#0
    //        && Civl_j#0 <= n
    //        && (forall i: int :: 
    //         1 <= i && i <= Civl_j#0 ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i])
    //        && Civl_j#0 < n
    //        && true
    //        && Civl_PAs_main_s == MapConst_3_8612(0)
    //        && pSet
    //          == Set_Union_4272(old(pSet), 
    //           Set_4272((lambda x: Permission :: 
    //               x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
    //        && Civl_PAs_read_f
    //          == MapAdd_8569(MapConst_3_8580(0), 
    //           MapIte_8587_3((lambda {:pool "C"} pa: read_f :: 
    //               Civl_j#0 + 1 <= pa->perm->val->mem_index
    //                  && pa->perm->val->mem_index <= n
    //                  && pa->perm->val->t_id == tid), 
    //             MapConst_3_8580(1), 
    //             MapConst_3_8580(0))))
    //    || 
       
     
        // assert (forall i: int :: 1 <= i && i <= Civl_j#0 ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i]);
          
      
           
          assert Civl_PAs_read_f == MapConst_3_8580(0);
          assert pSet == Set_Union_4272(old(pSet), Set_4272((lambda x: Permission :: x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)));
           
          assert Civl_PAs_main_s== MapAdd_8601(MapConst_3_8612(0), MapConst_3_8612(0)[main_s(tid) := 1]);
    return;
}



procedure Civl_ISR_SideCondition_read_f(perm: One_4565)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3379(One_Collector_4565(perm), 
          MapEq_4272_3(Civl_partition_Permission, MapConst_3_4272(0)))
         == MapConst_5_3379(true)
       && MapImp_3379(Set_Collector_4272(pSet), 
          MapEq_4272_3(Civl_partition_Permission, MapConst_3_4272(1)))
         == MapConst_5_3379(true));
  modifies r1, pSet;



implementation Civl_ISR_SideCondition_read_f(perm: One_4565)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int)
{

  init:
    call Civl_PAs_read_f, Civl_PAs_main_s := read_f(perm);
    goto Permission_only_put_perm_read_f;

  Permission_only_put_perm_read_f:
    assume true;
    assert MapImp_3379(old(MapOr_4272(Set_Collector_4272(pSet), MapConst_5_3379(false))), 
        MapOr_4272(Set_Collector_4272(pSet), MapConst_5_3379(false)))
       == MapConst_5_3379(true);
    return;
}


