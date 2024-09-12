// Boogie program verifier version 3.1.6.0, Copyright (c) 2003-2014, Microsoft.
// Command Line Options: snapshot-scatter-gather-old.bpl /civlDesugaredFile:namratha.bpl

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

var pSet: Set_4276;

function {:inline} WholeTidPermission(tid: Tid) : Set_4276
{
  Set_4276((lambda {:pool "D"} x: Permission :: 
      x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n))
}

datatype main_f {
  main_f(tid: Tid, sps: Set_4276)
}

datatype read_f {
  read_f(perm: One_4569)
}

datatype main_s {
  main_s(tid: Tid)
}

const Identity: [int]int;

function {:inline} AtLeast(x: int) : [int]bool
{
  MapLe_1305(MapConst_1322_1305(x), Identity)
}

function {:inline} Range(from: int, n: int) : [int]bool
{
  MapDiff_1325(AtLeast(from), AtLeast(from + n))
}

type {:builtin "Seq"} Seq _;

pure procedure Assume(b: bool);
  ensures b;



datatype Set_4276 {
  Set_4276(val: [Permission]bool)
}

pure procedure Set_Get_3382(path: Set_4276, k: [Permission]bool) returns (l: Set_4276);



procedure create_async_3353(PA: main_f);



datatype One_4569 {
  One_4569(val: Permission)
}

procedure create_asyncs_3404(PAs: [read_f]bool);



pure procedure Set_Put_3382(path: Set_4276, l: Set_4276);



procedure create_async_3358(PA: main_s);



function {:inline} Set_Add_3382(a: Set_4276, t: Permission) : Set_4276
{
  Set_4276(a->val[t := true])
}

function {:inline} Set_IsSubset_3385(a: Set_4276, b: Set_4276) : bool
{
  IsSubset_3385(a->val, b->val)
}

function {:inline} IsSubset_3385(a: [Permission]bool, b: [Permission]bool) : bool
{
  MapImp_3385(a, b) == MapConst_5_3385(true)
}

function {:builtin "MapImp"} MapImp_3385([Permission]bool, [Permission]bool) : [Permission]bool;

function {:builtin "MapConst"} MapConst_5_3385(bool) : [Permission]bool;

pure procedure One_Put_3382(path: Set_4276, l: One_4569);



procedure set_choice_3444(choice: read_f);



function {:builtin "MapConst"} MapConst_1322_1305(int) : [int]int;

function {:builtin "MapLe"} MapLe_1305([int]int, [int]int) : [int]bool;

function {:inline} MapDiff_1325(a: [int]bool, b: [int]bool) : [int]bool
{
  MapAnd_1325(a, MapNot_1325(b))
}

function {:builtin "MapNot"} MapNot_1325([int]bool) : [int]bool;

function {:builtin "MapAnd"} MapAnd_1325([int]bool, [int]bool) : [int]bool;

datatype Vec_5 {
  Vec_5(contents: [int]bool, len: int)
}

function Default_5() : bool;

function {:builtin "MapConst"} MapConst_5_1346(bool) : [int]bool;

function {:builtin "MapIte"} MapIte_1346_5([int]bool, [int]bool, [int]bool) : [int]bool;

datatype Vec_1322 {
  Vec_1322(contents: [int]int, len: int)
}

function Default_1322() : int;

function {:builtin "MapIte"} MapIte_1346_1322([int]bool, [int]int, [int]int) : [int]int;

function {:inline} Set_Empty_4276() : Set_4276
{
  Set_4276(MapConst_5_3385(false))
}

function Set_Size_4276(a: Set_4276) : int;

function {:inline} Set_Contains_4276(a: Set_4276, t: Permission) : bool
{
  a->val[t]
}

function {:inline} Set_Remove_4276(a: Set_4276, t: Permission) : Set_4276
{
  Set_4276(a->val[t := false])
}

function {:inline} Set_Difference_4276(a: Set_4276, b: Set_4276) : Set_4276
{
  Set_4276(MapDiff_4276(a->val, b->val))
}

function {:inline} MapDiff_4276(a: [Permission]bool, b: [Permission]bool) : [Permission]bool
{
  MapAnd_4276(a, MapNot_4276(b))
}

function {:builtin "MapNot"} MapNot_4276([Permission]bool) : [Permission]bool;

function {:builtin "MapAnd"} MapAnd_4276([Permission]bool, [Permission]bool) : [Permission]bool;

function {:inline} Set_Intersection_4276(a: Set_4276, b: Set_4276) : Set_4276
{
  Set_4276(MapAnd_4276(a->val, b->val))
}

function {:inline} Set_Union_4276(a: Set_4276, b: Set_4276) : Set_4276
{
  Set_4276(MapOr_4276(a->val, b->val))
}

function {:builtin "MapOr"} MapOr_4276([Permission]bool, [Permission]bool) : [Permission]bool;

function Choice_3385(a: [Permission]bool) : Permission;

function Choice_1305(a: [int]bool) : int;

axiom n >= 1;

axiom (forall x: int :: Identity[x] == x);

axiom (forall x: Vec_1322 :: 
  { x->len } { x->contents } 
  MapIte_1346_1322(Range(0, x->len), MapConst_1322_1305(Default_1322()), x->contents)
     == MapConst_1322_1305(Default_1322()));

axiom (forall x: Vec_5 :: 
  { x->len } { x->contents } 
  MapIte_1346_5(Range(0, x->len), MapConst_5_1346(Default_5()), x->contents)
     == MapConst_5_1346(Default_5()));

axiom (forall x: Vec_1322 :: { x->len } x->len >= 0);

axiom (forall x: Vec_5 :: { x->len } x->len >= 0);

axiom (forall a: Set_4276 :: a == Set_Empty_4276() || 0 < Set_Size_4276(a));

axiom Set_Size_4276(Set_Empty_4276()) == 0;

axiom (forall a: Set_4276, t: Permission :: 
  { Set_Add_3382(a, t) } 
  Set_Size_4276(Set_Add_3382(a, t))
     == (if Set_Contains_4276(a, t) then Set_Size_4276(a) else Set_Size_4276(a) + 1));

axiom (forall a: Set_4276, t: Permission :: 
  { Set_Remove_4276(a, t) } 
  Set_Size_4276(Set_Remove_4276(a, t))
     == (if Set_Contains_4276(a, t) then Set_Size_4276(a) - 1 else Set_Size_4276(a)));

axiom (forall a: Set_4276, b: Set_4276 :: 
  { Set_Difference_4276(a, b) } 
    { Set_Intersection_4276(a, b) } 
    { Set_Union_4276(a, b) } 
  Set_Size_4276(a)
     == Set_Size_4276(Set_Difference_4276(a, b))
       + Set_Size_4276(Set_Intersection_4276(a, b)));

axiom (forall a: Set_4276, b: Set_4276 :: 
  { Set_Union_4276(a, b) } { Set_Intersection_4276(a, b) } 
  Set_Size_4276(Set_Union_4276(a, b)) + Set_Size_4276(Set_Intersection_4276(a, b))
     == Set_Size_4276(a) + Set_Size_4276(b));

axiom (forall a: [int]bool :: 
  { Choice_1305(a) } 
  a == MapConst_5_1346(false) || a[Choice_1305(a)]);

axiom (forall a: [Permission]bool :: 
  { Choice_3385(a) } 
  a == MapConst_5_3385(false) || a[Choice_3385(a)]);

function {:builtin "MapConst"} MapConst_3_4276(int) : [Permission]int;

function {:builtin "MapEq"} MapEq_4276_3([Permission]int, [Permission]int) : [Permission]bool;

function {:builtin "MapAdd"} MapAdd_4276([Permission]int, [Permission]int) : [Permission]int;

function {:builtin "MapIte"} MapIte_4276_3([Permission]bool, [Permission]int, [Permission]int) : [Permission]int;

function {:builtin "MapLe"} MapLe_4276([Permission]int, [Permission]int) : [Permission]bool;

function {:inline} Set_Collector_4276(a: Set_4276) : [Permission]bool
{
  a->val
}

function {:inline} One_Collector_4569(a: One_4569) : [Permission]bool
{
  MapOne_4569(a->val)
}

function {:inline} MapOne_4569(t: Permission) : [Permission]bool
{
  MapConst_5_3385(false)[t := true]
}

function {:inline} Collector_read_f_Permission(target: read_f) : [Permission]bool
{
  (if target is read_f
     then MapOr_4276(One_Collector_4569(target->perm), MapConst_5_3385(false))
     else MapConst_5_3385(false))
}

function {:inline} Collector_main_f_Permission(target: main_f) : [Permission]bool
{
  (if target is main_f
     then MapOr_4276(Set_Collector_4276(target->sps), MapConst_5_3385(false))
     else MapConst_5_3385(false))
}

function {:builtin "MapAdd"} MapAdd_8759([main_f]int, [main_f]int) : [main_f]int;

function {:builtin "MapConst"} MapConst_3_8770(int) : [main_f]int;

function {:builtin "MapIte"} MapIte_8777_3([main_f]bool, [main_f]int, [main_f]int) : [main_f]int;

function {:builtin "MapAdd"} MapAdd_8791([read_f]int, [read_f]int) : [read_f]int;

function {:builtin "MapConst"} MapConst_3_8802(int) : [read_f]int;

function {:builtin "MapIte"} MapIte_8809_3([read_f]bool, [read_f]int, [read_f]int) : [read_f]int;

function {:builtin "MapAdd"} MapAdd_8823([main_s]int, [main_s]int) : [main_s]int;

function {:builtin "MapConst"} MapConst_3_8834(int) : [main_s]int;

function {:builtin "MapIte"} MapIte_8841_3([main_s]bool, [main_s]int, [main_s]int) : [main_s]int;

datatype Choice_Inv_f {
  Choice_Inv_f_read_f(read_f: read_f),
  Choice_Inv_f_main_s(main_s: main_s)
}

function Trigger_start_sps(sps: Set_4276) : bool;

function Trigger_main_f'_sps2(sps2: Set_4276) : bool;

function Trigger_main_f'_done_set(done_set: Set_4276) : bool;

function Trigger_read_f_k(k: int) : bool;

function Trigger_read_f_v(v: Value) : bool;

function Trigger_write_x(x: StampedValue) : bool;

function Trigger_Inv_f_j(j: int) : bool;

function Trigger_Inv_f_sps2(sps2: Set_4276) : bool;

function Trigger_Inv_f_done_set(done_set: Set_4276) : bool;

function Trigger_Inv_f_choice(choice: read_f) : bool;

implementation start(tid: Tid) returns (Civl_PAs_main_f: [main_f]int)
{
  var sps: Set_4276;

  /*** structured program:
    call sps := Set_Get_3382(pSet, (lambda x: Permission :: 
      x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
    call create_async_3353(main_f(tid, sps));
  **** end structured program */

  anon0:
    Civl_PAs_main_f := MapConst_3_8770(0);
    sps := Set_4276((lambda x: Permission :: 
        x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
    pSet := Set_Difference_4276(pSet, sps);
    Civl_PAs_main_f := MapAdd_8759(Civl_PAs_main_f, MapConst_3_8770(0)[main_f(tid, sps) := 1]);
    return;
}



procedure {:inline 1} start(tid: Tid) returns (Civl_PAs_main_f: [main_f]int);
  modifies pSet;



function {:inline} Civl_InputOutputRelation_start(tid: Tid, Civl_PAs_main_f: [main_f]int) : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_r1: [Tid][int]StampedValue, 
      Civl_old_r2: [Tid][int]StampedValue, 
      Civl_old_pSet: Set_4276, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4276 :: 
    Set_IsSubset_3385(Set_4276((lambda x: Permission :: 
            x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n)), 
        Civl_old_pSet)
       && 
      Civl_pSet
         == Set_Difference_4276(Civl_old_pSet, 
          Set_4276((lambda x: Permission :: 
              x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n)))
       && Civl_PAs_main_f
         == MapAdd_8759(MapConst_3_8770(0), 
          MapConst_3_8770(0)[main_f(tid, 
            Set_4276((lambda x: Permission :: 
                x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n))) := 1]))
}

implementation main_f'(tid: Tid, sps: Set_4276) returns (Civl_PAs_main_s: [main_s]int)
{
  var sps2: Set_4276;
  var done_set: Set_4276;

  /*** structured program:
    sps2 := sps;
    assume {:add_to_pool "A", 0, n} true;
    assert sps
       == Set_4276((lambda x: Permission :: 
          x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
    havoc r1;
    assume (forall i: int :: 
      1 <= i && i <= n ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i]);
    call done_set := Set_Get_3382(sps2, (lambda x: Permission :: 
      x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
    call Set_Put_3382(pSet, done_set);
    call create_async_3358(main_s(tid));
  **** end structured program */

  anon0:
    Civl_PAs_main_s := MapConst_3_8834(0);
    sps2 := sps;
    assume {:add_to_pool "A", 0, n} true;
    havoc r1;
    assume (forall i: int :: 
      1 <= i && i <= n ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i]);
    done_set := Set_4276((lambda x: Permission :: 
        x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
    sps2 := Set_Difference_4276(sps2, done_set);
    pSet := Set_Union_4276(pSet, done_set);
    Civl_PAs_main_s := MapAdd_8823(Civl_PAs_main_s, MapConst_3_8834(0)[main_s(tid) := 1]);
    return;
}



procedure {:inline 1} main_f'(tid: Tid, sps: Set_4276) returns (Civl_PAs_main_s: [main_s]int);
  modifies r1, pSet;



function {:inline} Civl_InputOutputRelation_main_f'(tid: Tid, sps: Set_4276, Civl_PAs_main_s: [main_s]int) : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_r1: [Tid][int]StampedValue, 
      Civl_old_r2: [Tid][int]StampedValue, 
      Civl_old_pSet: Set_4276, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4276 :: 
    (true
         ==> (forall r1: [Tid][int]StampedValue :: 
          (forall i: int :: 
              1 <= i && i <= n
                 ==> r1[tid][i]->ts < Civl_old_mem[i]->ts || r1[tid][i] == Civl_old_mem[i])
             ==> Set_IsSubset_3385(Set_4276((lambda x: Permission :: 
                  x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n)), 
              sps)))
       && (true
         ==> sps
           == Set_4276((lambda x: Permission :: 
              x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n)))
       && 
      true
       && (forall i: int :: 
        1 <= i && i <= n
           ==> Civl_r1[tid][i]->ts < Civl_mem[i]->ts || Civl_r1[tid][i] == Civl_mem[i])
       && Civl_pSet
         == Set_Union_4276(Civl_old_pSet, 
          Set_4276((lambda x: Permission :: 
              x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n)))
       && Civl_PAs_main_s
         == MapAdd_8823(MapConst_3_8834(0), MapConst_3_8834(0)[main_s(tid) := 1]))
}

implementation read_f(perm: One_4569)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int)
{
  var {:pool "K"} k: int;
  var {:pool "V"} v: Value;

  /*** structured program:
    assert 1 <= perm->val->mem_index && perm->val->mem_index <= n;
    assume {:add_to_pool "A", 0, n} true;
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

    call One_Put_3382(pSet, perm);
    if (Set_IsSubset(WholeTidPermission(perm->val->t_id), pSet))
    {
        call create_async(main_s(perm->val->t_id));
    }
  **** end structured program */

  anon0:
    assume Trigger_read_f_v(v);
    assume Trigger_read_f_k(k);
    Civl_PAs_read_f, Civl_PAs_main_s := MapConst_3_8802(0), MapConst_3_8834(0);
    assume {:add_to_pool "A", 0, n} true;
    goto anon5_Then, anon5_Else;

  anon5_Else:
    r1[perm->val->t_id][perm->val->mem_index] := mem[perm->val->mem_index];
    goto anon3;

  anon3:
    pSet := Set_Add_3382(pSet, perm->val);
    goto anon6_Then, anon6_Else;

  anon6_Else:
    assume {:partition} !Set_IsSubset_3385(WholeTidPermission(perm->val->t_id), pSet);
    return;

  anon6_Then:
    assume {:partition} Set_IsSubset_3385(WholeTidPermission(perm->val->t_id), pSet);
    Civl_PAs_main_s := MapAdd_8823(Civl_PAs_main_s, MapConst_3_8834(0)[main_s(perm->val->t_id) := 1]);
    return;

  anon5_Then:
    assume {:add_to_pool "K", mem[perm->val->mem_index]->ts, k} {:add_to_pool "V", mem[perm->val->mem_index]->value, v} true;
    assume k < mem[perm->val->mem_index]->ts;
    r1[perm->val->t_id][perm->val->mem_index] := StampedValue(k, v);
    goto anon3;
}



procedure {:inline 1} read_f(perm: One_4569)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int);
  modifies r1, pSet;



function {:inline} Civl_InputOutputRelation_read_f(perm: One_4569, Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int)
   : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_r1: [Tid][int]StampedValue, 
      Civl_old_r2: [Tid][int]StampedValue, 
      Civl_old_pSet: Set_4276, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4276 :: 
    1 <= perm->val->mem_index
       && perm->val->mem_index <= n
       && (
        (exists {:pool "K"} Civl_k#0: int, {:pool "V"} Civl_v#0: Value :: 
          true
             && true
             && Civl_k#0 < Civl_mem[perm->val->mem_index]->ts
             && Set_IsSubset_3385(WholeTidPermission(perm->val->t_id), Civl_pSet)
             && Civl_PAs_read_f == MapConst_3_8802(0)
             && Civl_r1
               == Civl_old_r1[perm->val->t_id := Civl_old_r1[perm->val->t_id][perm->val->mem_index := StampedValue(Civl_k#0, Civl_v#0)]]
             && Civl_pSet == Set_Add_3382(Civl_old_pSet, perm->val)
             && Civl_PAs_main_s
               == MapAdd_8823(MapConst_3_8834(0), MapConst_3_8834(0)[main_s(perm->val->t_id) := 1]))
         || (exists {:pool "K"} Civl_k#0: int, {:pool "V"} Civl_v#0: Value :: 
          true
             && true
             && Civl_k#0 < Civl_mem[perm->val->mem_index]->ts
             && !Set_IsSubset_3385(WholeTidPermission(perm->val->t_id), Civl_pSet)
             && Civl_PAs_read_f == MapConst_3_8802(0)
             && Civl_PAs_main_s == MapConst_3_8834(0)
             && Civl_r1
               == Civl_old_r1[perm->val->t_id := Civl_old_r1[perm->val->t_id][perm->val->mem_index := StampedValue(Civl_k#0, Civl_v#0)]]
             && Civl_pSet == Set_Add_3382(Civl_old_pSet, perm->val))
         || (
          true
           && Set_IsSubset_3385(WholeTidPermission(perm->val->t_id), Civl_pSet)
           && Civl_PAs_read_f == MapConst_3_8802(0)
           && Civl_r1
             == Civl_old_r1[perm->val->t_id := Civl_old_r1[perm->val->t_id][perm->val->mem_index := Civl_mem[perm->val->mem_index]]]
           && Civl_pSet == Set_Add_3382(Civl_old_pSet, perm->val)
           && Civl_PAs_main_s
             == MapAdd_8823(MapConst_3_8834(0), MapConst_3_8834(0)[main_s(perm->val->t_id) := 1]))
         || (
          true
           && !Set_IsSubset_3385(WholeTidPermission(perm->val->t_id), Civl_pSet)
           && Civl_PAs_read_f == MapConst_3_8802(0)
           && Civl_PAs_main_s == MapConst_3_8834(0)
           && Civl_r1
             == Civl_old_r1[perm->val->t_id := Civl_old_r1[perm->val->t_id][perm->val->mem_index := Civl_mem[perm->val->mem_index]]]
           && Civl_pSet == Set_Add_3382(Civl_old_pSet, perm->val))))
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
      Civl_old_pSet: Set_4276, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4276 :: 
    Civl_mem == Civl_old_mem[i := StampedValue(Civl_old_mem[i]->ts + 1, v)])
}

implementation Inv_f(tid: Tid, sps: Set_4276)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int)
{
  var {:pool "A"} j: int;
  var sps2: Set_4276;
  var done_set: Set_4276;
  var choice: read_f;

  /*** structured program:
    sps2 := sps;
    assert sps == WholeTidPermission(tid);
    assume {:add_to_pool "A", 0, j + 1, n} 0 <= j && j <= n;
    havoc r1;
    assume (forall i: int :: 
      1 <= i && i <= j ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i]);
    assume {:add_to_pool "D", Permission(tid, n)} true;
    call done_set := Set_Get_3382(sps2, (lambda {:pool "D"} x: Permission :: 
      x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j));
    call Set_Put_3382(pSet, done_set);
    if (j < n)
    {
        choice := read_f(One_4569(Permission(tid, j + 1)));
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
    Civl_PAs_read_f, Civl_PAs_main_s := MapConst_3_8802(0), MapConst_3_8834(0);
    sps2 := sps;
    assume {:add_to_pool "A", 0, j + 1, n} 0 <= j && j <= n;
    havoc r1;
    assume (forall i: int :: 
      1 <= i && i <= j ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i]);
    assume {:add_to_pool "D", Permission(tid, n)} true;
    done_set := Set_4276((lambda {:pool "D"} x: Permission :: 
        x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j));
    sps2 := Set_Difference_4276(sps2, done_set);
    pSet := Set_Union_4276(pSet, done_set);
    goto anon3_Then, anon3_Else;

  anon3_Else:
    assume {:partition} n <= j;
    Civl_PAs_main_s := MapAdd_8823(Civl_PAs_main_s, MapConst_3_8834(0)[main_s(tid) := 1]);
    return;

  anon3_Then:
    assume {:partition} j < n;
    choice := read_f(One_4569(Permission(tid, j + 1)));
    assume {:add_to_pool "C", choice} true;
    Civl_PAs_read_f := MapAdd_8791(Civl_PAs_read_f, 
      MapIte_8809_3((lambda {:pool "C"} pa: read_f :: 
          j + 1 <= pa->perm->val->mem_index
             && pa->perm->val->mem_index <= n
             && pa->perm->val->t_id == tid), 
        MapConst_3_8802(1), 
        MapConst_3_8802(0)));
    return;
}



procedure {:inline 1} Inv_f(tid: Tid, sps: Set_4276)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int);
  modifies r1, pSet;



function {:inline} Civl_InputOutputRelation_Inv_f(tid: Tid, 
    sps: Set_4276, 
    Civl_PAs_read_f: [read_f]int, 
    Civl_PAs_main_s: [main_s]int)
   : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_r1: [Tid][int]StampedValue, 
      Civl_old_r2: [Tid][int]StampedValue, 
      Civl_old_pSet: Set_4276, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4276 :: 
    (forall j: int :: 
        0 <= j && j <= n
           ==> (forall r1: [Tid][int]StampedValue :: 
            (forall i: int :: 
                1 <= i && i <= j
                   ==> r1[tid][i]->ts < Civl_old_mem[i]->ts || r1[tid][i] == Civl_old_mem[i])
               ==> 
              true
               ==> Set_IsSubset_3385(Set_4276((lambda {:pool "D"} x: Permission :: 
                    x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j)), 
                sps)))
       && sps == WholeTidPermission(tid)
       && ((exists {:pool "A"} Civl_j#0: int :: 
          0 <= Civl_j#0
             && Civl_j#0 <= n
             && (forall i: int :: 
              1 <= i && i <= Civl_j#0
                 ==> Civl_r1[tid][i]->ts < Civl_mem[i]->ts || Civl_r1[tid][i] == Civl_mem[i])
             && true
             && Civl_j#0 < n
             && true
             && Civl_PAs_main_s == MapConst_3_8834(0)
             && Civl_pSet
               == Set_Union_4276(Civl_old_pSet, 
                Set_4276((lambda {:pool "D"} x: Permission :: 
                    x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
             && Civl_PAs_read_f
               == MapAdd_8791(MapConst_3_8802(0), 
                MapIte_8809_3((lambda {:pool "C"} pa: read_f :: 
                    Civl_j#0 + 1 <= pa->perm->val->mem_index
                       && pa->perm->val->mem_index <= n
                       && pa->perm->val->t_id == tid), 
                  MapConst_3_8802(1), 
                  MapConst_3_8802(0))))
         || (exists {:pool "A"} Civl_j#0: int :: 
          0 <= Civl_j#0
             && Civl_j#0 <= n
             && (forall i: int :: 
              1 <= i && i <= Civl_j#0
                 ==> Civl_r1[tid][i]->ts < Civl_mem[i]->ts || Civl_r1[tid][i] == Civl_mem[i])
             && true
             && n <= Civl_j#0
             && Civl_PAs_read_f == MapConst_3_8802(0)
             && Civl_pSet
               == Set_Union_4276(Civl_old_pSet, 
                Set_4276((lambda {:pool "D"} x: Permission :: 
                    x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
             && Civl_PAs_main_s
               == MapAdd_8823(MapConst_3_8834(0), MapConst_3_8834(0)[main_s(tid) := 1]))))
}

implementation Inv_f_With_Choice(tid: Tid, sps: Set_4276)
   returns (Civl_PAs_read_f: [read_f]int, 
    Civl_PAs_main_s: [main_s]int, 
    Civl_choice: Choice_Inv_f)
{
  var {:pool "A"} j: int;
  var sps2: Set_4276;
  var done_set: Set_4276;
  var choice: read_f;

  /*** structured program:
    sps2 := sps;
    assert sps == WholeTidPermission(tid);
    assume {:add_to_pool "A", 0, j + 1, n} 0 <= j && j <= n;
    havoc r1;
    assume (forall i: int :: 
      1 <= i && i <= j ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i]);
    assume {:add_to_pool "D", Permission(tid, n)} true;
    call done_set := Set_Get_3382(sps2, (lambda {:pool "D"} x: Permission :: 
      x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j));
    call Set_Put_3382(pSet, done_set);
    if (j < n)
    {
        choice := read_f(One_4569(Permission(tid, j + 1)));
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
    Civl_PAs_read_f, Civl_PAs_main_s := MapConst_3_8802(0), MapConst_3_8834(0);
    sps2 := sps;
    assert sps == WholeTidPermission(tid);
    assume {:add_to_pool "A", 0, j + 1, n} 0 <= j && j <= n;
    havoc r1;
    assume (forall i: int :: 
      1 <= i && i <= j ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i]);
    assume {:add_to_pool "D", Permission(tid, n)} true;
    done_set := Set_4276((lambda {:pool "D"} x: Permission :: 
        x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j));
    assert Set_IsSubset_3385(done_set, sps2);
    sps2 := Set_Difference_4276(sps2, done_set);
    pSet := Set_Union_4276(pSet, done_set);
    goto anon3_Then, anon3_Else;

  anon3_Else:
    assume {:partition} n <= j;
    Civl_PAs_main_s := MapAdd_8823(Civl_PAs_main_s, MapConst_3_8834(0)[main_s(tid) := 1]);
    return;

  anon3_Then:
    assume {:partition} j < n;
    choice := read_f(One_4569(Permission(tid, j + 1)));
    assume {:add_to_pool "C", choice} true;
    Civl_PAs_read_f := MapAdd_8791(Civl_PAs_read_f, 
      MapIte_8809_3((lambda {:pool "C"} pa: read_f :: 
          j + 1 <= pa->perm->val->mem_index
             && pa->perm->val->mem_index <= n
             && pa->perm->val->t_id == tid), 
        MapConst_3_8802(1), 
        MapConst_3_8802(0)));
    assert Civl_PAs_read_f == MapConst_3_8802(0) || Civl_PAs_read_f[choice] > 0;
    Civl_choice->read_f := choice;
    return;
}



procedure {:inline 1} Inv_f_With_Choice(tid: Tid, sps: Set_4276)
   returns (Civl_PAs_read_f: [read_f]int, 
    Civl_PAs_main_s: [main_s]int, 
    Civl_choice: Choice_Inv_f);
  modifies r1, pSet;



function {:inline} Civl_InputOutputRelation_Inv_f_With_Choice(tid: Tid, 
    sps: Set_4276, 
    Civl_PAs_read_f: [read_f]int, 
    Civl_PAs_main_s: [main_s]int, 
    Civl_choice: Choice_Inv_f)
   : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_r1: [Tid][int]StampedValue, 
      Civl_old_r2: [Tid][int]StampedValue, 
      Civl_old_pSet: Set_4276, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4276 :: 
    (forall j: int :: 
        0 <= j && j <= n
           ==> (forall r1: [Tid][int]StampedValue :: 
            (forall i: int :: 
                1 <= i && i <= j
                   ==> r1[tid][i]->ts < Civl_old_mem[i]->ts || r1[tid][i] == Civl_old_mem[i])
               ==> 
              true
               ==> Set_IsSubset_3385(Set_4276((lambda {:pool "D"} x: Permission :: 
                    x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j)), 
                sps)))
       && sps == WholeTidPermission(tid)
       && ((exists {:pool "A"} Civl_j#0: int :: 
          sps == WholeTidPermission(tid)
             && 0 <= Civl_j#0
             && Civl_j#0 <= n
             && (forall i: int :: 
              1 <= i && i <= Civl_j#0
                 ==> Civl_r1[tid][i]->ts < Civl_mem[i]->ts || Civl_r1[tid][i] == Civl_mem[i])
             && true
             && Set_IsSubset_3385(Set_4276((lambda {:pool "D"} x: Permission :: 
                  x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)), 
              sps)
             && Civl_j#0 < n
             && true
             && (Civl_PAs_read_f == MapConst_3_8802(0)
               || Civl_PAs_read_f[read_f(One_4569(Permission(tid, Civl_j#0 + 1)))] > 0)
             && Civl_PAs_main_s == MapConst_3_8834(0)
             && Civl_pSet
               == Set_Union_4276(Civl_old_pSet, 
                Set_4276((lambda {:pool "D"} x: Permission :: 
                    x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
             && Civl_PAs_read_f
               == MapAdd_8791(MapConst_3_8802(0), 
                MapIte_8809_3((lambda {:pool "C"} pa: read_f :: 
                    Civl_j#0 + 1 <= pa->perm->val->mem_index
                       && pa->perm->val->mem_index <= n
                       && pa->perm->val->t_id == tid), 
                  MapConst_3_8802(1), 
                  MapConst_3_8802(0)))
             && Civl_choice
               == Choice_Inv_f_read_f(read_f(One_4569(Permission(tid, Civl_j#0 + 1)))))
         || (exists {:pool "A"} Civl_j#0: int :: 
          sps == WholeTidPermission(tid)
             && 0 <= Civl_j#0
             && Civl_j#0 <= n
             && (forall i: int :: 
              1 <= i && i <= Civl_j#0
                 ==> Civl_r1[tid][i]->ts < Civl_mem[i]->ts || Civl_r1[tid][i] == Civl_mem[i])
             && true
             && Set_IsSubset_3385(Set_4276((lambda {:pool "D"} x: Permission :: 
                  x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)), 
              sps)
             && n <= Civl_j#0
             && Civl_PAs_read_f == MapConst_3_8802(0)
             && Civl_pSet
               == Set_Union_4276(Civl_old_pSet, 
                Set_4276((lambda {:pool "D"} x: Permission :: 
                    x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
             && Civl_PAs_main_s
               == MapAdd_8823(MapConst_3_8834(0), MapConst_3_8834(0)[main_s(tid) := 1]))))
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
      Civl_old_pSet: Set_4276, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4276 :: 
    true)
}

implementation main_f(tid: Tid, sps: Set_4276) returns (Civl_PAs_read_f: [read_f]int)
{
  /*** structured program:
    assume {:add_to_pool "A", 0, n} true;
    assert sps
       == Set_4276((lambda x: Permission :: 
          x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
    call create_asyncs_3404((lambda pa: read_f :: 
      1 <= pa->perm->val->mem_index
         && pa->perm->val->mem_index <= n
         && pa->perm->val->t_id == tid));
  **** end structured program */

  anon0:
    Civl_PAs_read_f := MapConst_3_8802(0);
    assume {:add_to_pool "A", 0, n} true;
    Civl_PAs_read_f := MapAdd_8791(Civl_PAs_read_f, 
      MapIte_8809_3((lambda pa: read_f :: 
          1 <= pa->perm->val->mem_index
             && pa->perm->val->mem_index <= n
             && pa->perm->val->t_id == tid), 
        MapConst_3_8802(1), 
        MapConst_3_8802(0)));
    return;
}



procedure {:inline 1} main_f(tid: Tid, sps: Set_4276) returns (Civl_PAs_read_f: [read_f]int);
  modifies pSet;



function {:inline} Civl_InputOutputRelation_main_f(tid: Tid, sps: Set_4276, Civl_PAs_read_f: [read_f]int) : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_r1: [Tid][int]StampedValue, 
      Civl_old_r2: [Tid][int]StampedValue, 
      Civl_old_pSet: Set_4276, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4276 :: 
    (true
         ==> sps
           == Set_4276((lambda x: Permission :: 
              x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n)))
       && 
      true
       && Civl_PAs_read_f
         == MapAdd_8791(MapConst_3_8802(0), 
          MapIte_8809_3((lambda pa: read_f :: 
              1 <= pa->perm->val->mem_index
                 && pa->perm->val->mem_index <= n
                 && pa->perm->val->t_id == tid), 
            MapConst_3_8802(1), 
            MapConst_3_8802(0)))
       && Civl_pSet == Civl_old_pSet)
}

implementation Civl_CommutativityChecker_read_f_start_1(first_perm: One_4569, second_tid: Tid)
   returns (first_Civl_PAs_read_f: [read_f]int, 
    first_Civl_PAs_main_s: [main_s]int, 
    second_Civl_PAs_main_f: [main_f]int)
{

  init:
    call first_Civl_PAs_read_f, first_Civl_PAs_main_s := read_f(first_perm);
    call second_Civl_PAs_main_f := start(second_tid);
    assert true
       ==> (exists {:pool "K"} Civl_first_k#0: int, {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && Set_IsSubset_3385(WholeTidPermission(first_perm->val->t_id), pSet)
             && second_Civl_PAs_main_f
               == MapAdd_8759(MapConst_3_8770(0), 
                MapConst_3_8770(0)[main_f(second_tid, 
                  Set_4276((lambda second_x: Permission :: 
                      second_x->t_id == second_tid
                         && 1 <= second_x->mem_index
                         && second_x->mem_index <= n))) := 1])
             && first_Civl_PAs_read_f == MapConst_3_8802(0)
             && r1
               == old(r1)[first_perm->val->t_id := old(r1)[first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet
               == Set_Add_3382(Set_Difference_4276(old(pSet), 
                  Set_4276((lambda second_x: Permission :: 
                      second_x->t_id == second_tid
                         && 1 <= second_x->mem_index
                         && second_x->mem_index <= n))), 
                first_perm->val)
             && first_Civl_PAs_main_s
               == MapAdd_8823(MapConst_3_8834(0), MapConst_3_8834(0)[main_s(first_perm->val->t_id) := 1])
             && mem == old(mem))
         || (exists {:pool "K"} Civl_first_k#0: int, {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && !Set_IsSubset_3385(WholeTidPermission(first_perm->val->t_id), pSet)
             && second_Civl_PAs_main_f
               == MapAdd_8759(MapConst_3_8770(0), 
                MapConst_3_8770(0)[main_f(second_tid, 
                  Set_4276((lambda second_x: Permission :: 
                      second_x->t_id == second_tid
                         && 1 <= second_x->mem_index
                         && second_x->mem_index <= n))) := 1])
             && first_Civl_PAs_read_f == MapConst_3_8802(0)
             && first_Civl_PAs_main_s == MapConst_3_8834(0)
             && r1
               == old(r1)[first_perm->val->t_id := old(r1)[first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet
               == Set_Add_3382(Set_Difference_4276(old(pSet), 
                  Set_4276((lambda second_x: Permission :: 
                      second_x->t_id == second_tid
                         && 1 <= second_x->mem_index
                         && second_x->mem_index <= n))), 
                first_perm->val)
             && mem == old(mem))
         || (
          true
           && Set_IsSubset_3385(WholeTidPermission(first_perm->val->t_id), pSet)
           && second_Civl_PAs_main_f
             == MapAdd_8759(MapConst_3_8770(0), 
              MapConst_3_8770(0)[main_f(second_tid, 
                Set_4276((lambda second_x: Permission :: 
                    second_x->t_id == second_tid
                       && 1 <= second_x->mem_index
                       && second_x->mem_index <= n))) := 1])
           && first_Civl_PAs_read_f == MapConst_3_8802(0)
           && r1
             == old(r1)[first_perm->val->t_id := old(r1)[first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet
             == Set_Add_3382(Set_Difference_4276(old(pSet), 
                Set_4276((lambda second_x: Permission :: 
                    second_x->t_id == second_tid
                       && 1 <= second_x->mem_index
                       && second_x->mem_index <= n))), 
              first_perm->val)
           && first_Civl_PAs_main_s
             == MapAdd_8823(MapConst_3_8834(0), MapConst_3_8834(0)[main_s(first_perm->val->t_id) := 1])
           && mem == old(mem))
         || (
          true
           && !Set_IsSubset_3385(WholeTidPermission(first_perm->val->t_id), pSet)
           && second_Civl_PAs_main_f
             == MapAdd_8759(MapConst_3_8770(0), 
              MapConst_3_8770(0)[main_f(second_tid, 
                Set_4276((lambda second_x: Permission :: 
                    second_x->t_id == second_tid
                       && 1 <= second_x->mem_index
                       && second_x->mem_index <= n))) := 1])
           && first_Civl_PAs_read_f == MapConst_3_8802(0)
           && first_Civl_PAs_main_s == MapConst_3_8834(0)
           && r1
             == old(r1)[first_perm->val->t_id := old(r1)[first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet
             == Set_Add_3382(Set_Difference_4276(old(pSet), 
                Set_4276((lambda second_x: Permission :: 
                    second_x->t_id == second_tid
                       && 1 <= second_x->mem_index
                       && second_x->mem_index <= n))), 
              first_perm->val)
           && mem == old(mem));
    return;
}



procedure Civl_CommutativityChecker_read_f_start_1(first_perm: One_4569, second_tid: Tid)
   returns (first_Civl_PAs_read_f: [read_f]int, 
    first_Civl_PAs_main_s: [main_s]int, 
    second_Civl_PAs_main_f: [main_f]int);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3385(One_Collector_4569(first_perm), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(0)))
         == MapConst_5_3385(true)
       && MapImp_3385(Set_Collector_4276(pSet), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(1)))
         == MapConst_5_3385(true));
  requires 1 <= first_perm->val->mem_index && first_perm->val->mem_index <= n;
  requires Set_IsSubset_3385(Set_4276((lambda second_x: Permission :: 
        second_x->t_id == second_tid
           && 1 <= second_x->mem_index
           && second_x->mem_index <= n)), 
    pSet);
  requires Set_IsSubset_3385(WholeTidPermission(first_perm->val->t_id), Set_Add_3382(pSet, first_perm->val));
  modifies mem, r1, r2, pSet;



implementation Civl_GatePreservationChecker_start_read_f_1(first_tid: Tid, second_perm: One_4569)
   returns (first_Civl_PAs_main_f: [main_f]int, 
    second_Civl_PAs_read_f: [read_f]int, 
    second_Civl_PAs_main_s: [main_s]int)
{

  init:
    call second_Civl_PAs_read_f, second_Civl_PAs_main_s := read_f(second_perm);
    assert true
       ==> Set_IsSubset_3385(Set_4276((lambda first_x: Permission :: 
            first_x->t_id == first_tid && 1 <= first_x->mem_index && first_x->mem_index <= n)), 
        pSet);
    return;
}



procedure Civl_GatePreservationChecker_start_read_f_1(first_tid: Tid, second_perm: One_4569)
   returns (first_Civl_PAs_main_f: [main_f]int, 
    second_Civl_PAs_read_f: [read_f]int, 
    second_Civl_PAs_main_s: [main_s]int);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3385(One_Collector_4569(second_perm), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(0)))
         == MapConst_5_3385(true)
       && MapImp_3385(Set_Collector_4276(pSet), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(1)))
         == MapConst_5_3385(true));
  requires Set_IsSubset_3385(Set_4276((lambda first_x: Permission :: 
        first_x->t_id == first_tid && 1 <= first_x->mem_index && first_x->mem_index <= n)), 
    pSet);
  requires 1 <= second_perm->val->mem_index && second_perm->val->mem_index <= n;
  requires Set_IsSubset_3385(WholeTidPermission(second_perm->val->t_id), Set_Add_3382(pSet, second_perm->val));
  modifies mem, r1, r2, pSet;



implementation Civl_CommutativityChecker_read_f_read_f_1(first_perm: One_4569, second_perm: One_4569)
   returns (first_Civl_PAs_read_f: [read_f]int, 
    first_Civl_PAs_main_s: [main_s]int, 
    second_Civl_PAs_read_f: [read_f]int, 
    second_Civl_PAs_main_s: [main_s]int)
{

  init:
    call first_Civl_PAs_read_f, first_Civl_PAs_main_s := read_f(first_perm);
    call second_Civl_PAs_read_f, second_Civl_PAs_main_s := read_f(second_perm);
    assert true
       ==> (exists {:pool "K"} Civl_second_k#0: int, 
            {:pool "K"} Civl_first_k#0: int, 
            {:pool "V"} Civl_second_v#0: Value, 
            {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_second_v#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && Set_IsSubset_3385(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3382(old(pSet), second_perm->val))
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && Set_IsSubset_3385(WholeTidPermission(first_perm->val->t_id), pSet)
             && second_Civl_PAs_read_f == MapConst_3_8802(0)
             && second_Civl_PAs_main_s
               == MapAdd_8823(MapConst_3_8834(0), MapConst_3_8834(0)[main_s(second_perm->val->t_id) := 1])
             && first_Civl_PAs_read_f == MapConst_3_8802(0)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3382(Set_Add_3382(old(pSet), second_perm->val), first_perm->val)
             && first_Civl_PAs_main_s
               == MapAdd_8823(MapConst_3_8834(0), MapConst_3_8834(0)[main_s(first_perm->val->t_id) := 1])
             && mem == old(mem))
         || (exists {:pool "K"} Civl_second_k#0: int, 
            {:pool "K"} Civl_first_k#0: int, 
            {:pool "V"} Civl_second_v#0: Value, 
            {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_second_v#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && Set_IsSubset_3385(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3382(old(pSet), second_perm->val))
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && !Set_IsSubset_3385(WholeTidPermission(first_perm->val->t_id), pSet)
             && second_Civl_PAs_read_f == MapConst_3_8802(0)
             && second_Civl_PAs_main_s
               == MapAdd_8823(MapConst_3_8834(0), MapConst_3_8834(0)[main_s(second_perm->val->t_id) := 1])
             && first_Civl_PAs_read_f == MapConst_3_8802(0)
             && first_Civl_PAs_main_s == MapConst_3_8834(0)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3382(Set_Add_3382(old(pSet), second_perm->val), first_perm->val)
             && mem == old(mem))
         || (exists {:pool "K"} Civl_second_k#0: int, {:pool "V"} Civl_second_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_v(Civl_second_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && Set_IsSubset_3385(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3382(old(pSet), second_perm->val))
             && true
             && Set_IsSubset_3385(WholeTidPermission(first_perm->val->t_id), pSet)
             && second_Civl_PAs_read_f == MapConst_3_8802(0)
             && second_Civl_PAs_main_s
               == MapAdd_8823(MapConst_3_8834(0), MapConst_3_8834(0)[main_s(second_perm->val->t_id) := 1])
             && first_Civl_PAs_read_f == MapConst_3_8802(0)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
             && pSet == Set_Add_3382(Set_Add_3382(old(pSet), second_perm->val), first_perm->val)
             && first_Civl_PAs_main_s
               == MapAdd_8823(MapConst_3_8834(0), MapConst_3_8834(0)[main_s(first_perm->val->t_id) := 1])
             && mem == old(mem))
         || (exists {:pool "K"} Civl_second_k#0: int, {:pool "V"} Civl_second_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_v(Civl_second_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && Set_IsSubset_3385(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3382(old(pSet), second_perm->val))
             && true
             && !Set_IsSubset_3385(WholeTidPermission(first_perm->val->t_id), pSet)
             && second_Civl_PAs_read_f == MapConst_3_8802(0)
             && second_Civl_PAs_main_s
               == MapAdd_8823(MapConst_3_8834(0), MapConst_3_8834(0)[main_s(second_perm->val->t_id) := 1])
             && first_Civl_PAs_read_f == MapConst_3_8802(0)
             && first_Civl_PAs_main_s == MapConst_3_8834(0)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
             && pSet == Set_Add_3382(Set_Add_3382(old(pSet), second_perm->val), first_perm->val)
             && mem == old(mem))
         || (exists {:pool "K"} Civl_second_k#0: int, 
            {:pool "K"} Civl_first_k#0: int, 
            {:pool "V"} Civl_second_v#0: Value, 
            {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_second_v#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && !Set_IsSubset_3385(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3382(old(pSet), second_perm->val))
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && Set_IsSubset_3385(WholeTidPermission(first_perm->val->t_id), pSet)
             && second_Civl_PAs_read_f == MapConst_3_8802(0)
             && second_Civl_PAs_main_s == MapConst_3_8834(0)
             && first_Civl_PAs_read_f == MapConst_3_8802(0)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3382(Set_Add_3382(old(pSet), second_perm->val), first_perm->val)
             && first_Civl_PAs_main_s
               == MapAdd_8823(MapConst_3_8834(0), MapConst_3_8834(0)[main_s(first_perm->val->t_id) := 1])
             && mem == old(mem))
         || (exists {:pool "K"} Civl_second_k#0: int, 
            {:pool "K"} Civl_first_k#0: int, 
            {:pool "V"} Civl_second_v#0: Value, 
            {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_second_v#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && !Set_IsSubset_3385(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3382(old(pSet), second_perm->val))
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && !Set_IsSubset_3385(WholeTidPermission(first_perm->val->t_id), pSet)
             && second_Civl_PAs_read_f == MapConst_3_8802(0)
             && second_Civl_PAs_main_s == MapConst_3_8834(0)
             && first_Civl_PAs_read_f == MapConst_3_8802(0)
             && first_Civl_PAs_main_s == MapConst_3_8834(0)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3382(Set_Add_3382(old(pSet), second_perm->val), first_perm->val)
             && mem == old(mem))
         || (exists {:pool "K"} Civl_second_k#0: int, {:pool "V"} Civl_second_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_v(Civl_second_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && !Set_IsSubset_3385(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3382(old(pSet), second_perm->val))
             && true
             && Set_IsSubset_3385(WholeTidPermission(first_perm->val->t_id), pSet)
             && second_Civl_PAs_read_f == MapConst_3_8802(0)
             && second_Civl_PAs_main_s == MapConst_3_8834(0)
             && first_Civl_PAs_read_f == MapConst_3_8802(0)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
             && pSet == Set_Add_3382(Set_Add_3382(old(pSet), second_perm->val), first_perm->val)
             && first_Civl_PAs_main_s
               == MapAdd_8823(MapConst_3_8834(0), MapConst_3_8834(0)[main_s(first_perm->val->t_id) := 1])
             && mem == old(mem))
         || (exists {:pool "K"} Civl_second_k#0: int, {:pool "V"} Civl_second_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_v(Civl_second_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && !Set_IsSubset_3385(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3382(old(pSet), second_perm->val))
             && true
             && !Set_IsSubset_3385(WholeTidPermission(first_perm->val->t_id), pSet)
             && second_Civl_PAs_read_f == MapConst_3_8802(0)
             && second_Civl_PAs_main_s == MapConst_3_8834(0)
             && first_Civl_PAs_read_f == MapConst_3_8802(0)
             && first_Civl_PAs_main_s == MapConst_3_8834(0)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
             && pSet == Set_Add_3382(Set_Add_3382(old(pSet), second_perm->val), first_perm->val)
             && mem == old(mem))
         || (exists {:pool "K"} Civl_first_k#0: int, {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && Set_IsSubset_3385(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3382(old(pSet), second_perm->val))
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && Set_IsSubset_3385(WholeTidPermission(first_perm->val->t_id), pSet)
             && second_Civl_PAs_read_f == MapConst_3_8802(0)
             && second_Civl_PAs_main_s
               == MapAdd_8823(MapConst_3_8834(0), MapConst_3_8834(0)[main_s(second_perm->val->t_id) := 1])
             && first_Civl_PAs_read_f == MapConst_3_8802(0)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3382(Set_Add_3382(old(pSet), second_perm->val), first_perm->val)
             && first_Civl_PAs_main_s
               == MapAdd_8823(MapConst_3_8834(0), MapConst_3_8834(0)[main_s(first_perm->val->t_id) := 1])
             && mem == old(mem))
         || (exists {:pool "K"} Civl_first_k#0: int, {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && Set_IsSubset_3385(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3382(old(pSet), second_perm->val))
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && !Set_IsSubset_3385(WholeTidPermission(first_perm->val->t_id), pSet)
             && second_Civl_PAs_read_f == MapConst_3_8802(0)
             && second_Civl_PAs_main_s
               == MapAdd_8823(MapConst_3_8834(0), MapConst_3_8834(0)[main_s(second_perm->val->t_id) := 1])
             && first_Civl_PAs_read_f == MapConst_3_8802(0)
             && first_Civl_PAs_main_s == MapConst_3_8834(0)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3382(Set_Add_3382(old(pSet), second_perm->val), first_perm->val)
             && mem == old(mem))
         || (
          true
           && Set_IsSubset_3385(WholeTidPermission(second_perm->val->t_id), 
            Set_Add_3382(old(pSet), second_perm->val))
           && true
           && Set_IsSubset_3385(WholeTidPermission(first_perm->val->t_id), pSet)
           && second_Civl_PAs_read_f == MapConst_3_8802(0)
           && second_Civl_PAs_main_s
             == MapAdd_8823(MapConst_3_8834(0), MapConst_3_8834(0)[main_s(second_perm->val->t_id) := 1])
           && first_Civl_PAs_read_f == MapConst_3_8802(0)
           && r1
             == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet == Set_Add_3382(Set_Add_3382(old(pSet), second_perm->val), first_perm->val)
           && first_Civl_PAs_main_s
             == MapAdd_8823(MapConst_3_8834(0), MapConst_3_8834(0)[main_s(first_perm->val->t_id) := 1])
           && mem == old(mem))
         || (
          true
           && Set_IsSubset_3385(WholeTidPermission(second_perm->val->t_id), 
            Set_Add_3382(old(pSet), second_perm->val))
           && true
           && !Set_IsSubset_3385(WholeTidPermission(first_perm->val->t_id), pSet)
           && second_Civl_PAs_read_f == MapConst_3_8802(0)
           && second_Civl_PAs_main_s
             == MapAdd_8823(MapConst_3_8834(0), MapConst_3_8834(0)[main_s(second_perm->val->t_id) := 1])
           && first_Civl_PAs_read_f == MapConst_3_8802(0)
           && first_Civl_PAs_main_s == MapConst_3_8834(0)
           && r1
             == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet == Set_Add_3382(Set_Add_3382(old(pSet), second_perm->val), first_perm->val)
           && mem == old(mem))
         || (exists {:pool "K"} Civl_first_k#0: int, {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && !Set_IsSubset_3385(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3382(old(pSet), second_perm->val))
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && Set_IsSubset_3385(WholeTidPermission(first_perm->val->t_id), pSet)
             && second_Civl_PAs_read_f == MapConst_3_8802(0)
             && second_Civl_PAs_main_s == MapConst_3_8834(0)
             && first_Civl_PAs_read_f == MapConst_3_8802(0)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3382(Set_Add_3382(old(pSet), second_perm->val), first_perm->val)
             && first_Civl_PAs_main_s
               == MapAdd_8823(MapConst_3_8834(0), MapConst_3_8834(0)[main_s(first_perm->val->t_id) := 1])
             && mem == old(mem))
         || (exists {:pool "K"} Civl_first_k#0: int, {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && !Set_IsSubset_3385(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3382(old(pSet), second_perm->val))
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && !Set_IsSubset_3385(WholeTidPermission(first_perm->val->t_id), pSet)
             && second_Civl_PAs_read_f == MapConst_3_8802(0)
             && second_Civl_PAs_main_s == MapConst_3_8834(0)
             && first_Civl_PAs_read_f == MapConst_3_8802(0)
             && first_Civl_PAs_main_s == MapConst_3_8834(0)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3382(Set_Add_3382(old(pSet), second_perm->val), first_perm->val)
             && mem == old(mem))
         || (
          true
           && !Set_IsSubset_3385(WholeTidPermission(second_perm->val->t_id), 
            Set_Add_3382(old(pSet), second_perm->val))
           && true
           && Set_IsSubset_3385(WholeTidPermission(first_perm->val->t_id), pSet)
           && second_Civl_PAs_read_f == MapConst_3_8802(0)
           && second_Civl_PAs_main_s == MapConst_3_8834(0)
           && first_Civl_PAs_read_f == MapConst_3_8802(0)
           && r1
             == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet == Set_Add_3382(Set_Add_3382(old(pSet), second_perm->val), first_perm->val)
           && first_Civl_PAs_main_s
             == MapAdd_8823(MapConst_3_8834(0), MapConst_3_8834(0)[main_s(first_perm->val->t_id) := 1])
           && mem == old(mem))
         || (
          true
           && !Set_IsSubset_3385(WholeTidPermission(second_perm->val->t_id), 
            Set_Add_3382(old(pSet), second_perm->val))
           && true
           && !Set_IsSubset_3385(WholeTidPermission(first_perm->val->t_id), pSet)
           && second_Civl_PAs_read_f == MapConst_3_8802(0)
           && second_Civl_PAs_main_s == MapConst_3_8834(0)
           && first_Civl_PAs_read_f == MapConst_3_8802(0)
           && first_Civl_PAs_main_s == MapConst_3_8834(0)
           && r1
             == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet == Set_Add_3382(Set_Add_3382(old(pSet), second_perm->val), first_perm->val)
           && mem == old(mem));
    return;
}



procedure Civl_CommutativityChecker_read_f_read_f_1(first_perm: One_4569, second_perm: One_4569)
   returns (first_Civl_PAs_read_f: [read_f]int, 
    first_Civl_PAs_main_s: [main_s]int, 
    second_Civl_PAs_read_f: [read_f]int, 
    second_Civl_PAs_main_s: [main_s]int);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3385(One_Collector_4569(first_perm), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(0)))
         == MapConst_5_3385(true)
       && MapImp_3385(One_Collector_4569(second_perm), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(1)))
         == MapConst_5_3385(true)
       && MapImp_3385(Set_Collector_4276(pSet), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(2)))
         == MapConst_5_3385(true));
  requires 1 <= first_perm->val->mem_index && first_perm->val->mem_index <= n;
  requires 1 <= second_perm->val->mem_index && second_perm->val->mem_index <= n;
  requires Set_IsSubset_3385(WholeTidPermission(first_perm->val->t_id), Set_Add_3382(pSet, first_perm->val));
  modifies mem, r1, r2, pSet;



implementation Civl_CommutativityChecker_read_f_write_1(first_perm: One_4569, second_i: int, second_v: Value)
   returns (first_Civl_PAs_read_f: [read_f]int, first_Civl_PAs_main_s: [main_s]int)
{

  init:
    call first_Civl_PAs_read_f, first_Civl_PAs_main_s := read_f(first_perm);
    call write(second_i, second_v);
    assert true
       ==> (exists {:pool "K"} Civl_first_k#0: int, {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && Set_IsSubset_3385(WholeTidPermission(first_perm->val->t_id), pSet)
             && mem == old(mem)[second_i := StampedValue(old(mem)[second_i]->ts + 1, second_v)]
             && first_Civl_PAs_read_f == MapConst_3_8802(0)
             && r1
               == old(r1)[first_perm->val->t_id := old(r1)[first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3382(old(pSet), first_perm->val)
             && first_Civl_PAs_main_s
               == MapAdd_8823(MapConst_3_8834(0), MapConst_3_8834(0)[main_s(first_perm->val->t_id) := 1]))
         || (exists {:pool "K"} Civl_first_k#0: int, {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && !Set_IsSubset_3385(WholeTidPermission(first_perm->val->t_id), pSet)
             && mem == old(mem)[second_i := StampedValue(old(mem)[second_i]->ts + 1, second_v)]
             && first_Civl_PAs_read_f == MapConst_3_8802(0)
             && first_Civl_PAs_main_s == MapConst_3_8834(0)
             && r1
               == old(r1)[first_perm->val->t_id := old(r1)[first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3382(old(pSet), first_perm->val))
         || (
          true
           && Set_IsSubset_3385(WholeTidPermission(first_perm->val->t_id), pSet)
           && mem == old(mem)[second_i := StampedValue(old(mem)[second_i]->ts + 1, second_v)]
           && first_Civl_PAs_read_f == MapConst_3_8802(0)
           && r1
             == old(r1)[first_perm->val->t_id := old(r1)[first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet == Set_Add_3382(old(pSet), first_perm->val)
           && first_Civl_PAs_main_s
             == MapAdd_8823(MapConst_3_8834(0), MapConst_3_8834(0)[main_s(first_perm->val->t_id) := 1]))
         || (
          true
           && !Set_IsSubset_3385(WholeTidPermission(first_perm->val->t_id), pSet)
           && mem == old(mem)[second_i := StampedValue(old(mem)[second_i]->ts + 1, second_v)]
           && first_Civl_PAs_read_f == MapConst_3_8802(0)
           && first_Civl_PAs_main_s == MapConst_3_8834(0)
           && r1
             == old(r1)[first_perm->val->t_id := old(r1)[first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet == Set_Add_3382(old(pSet), first_perm->val));
    return;
}



procedure Civl_CommutativityChecker_read_f_write_1(first_perm: One_4569, second_i: int, second_v: Value)
   returns (first_Civl_PAs_read_f: [read_f]int, first_Civl_PAs_main_s: [main_s]int);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3385(One_Collector_4569(first_perm), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(0)))
         == MapConst_5_3385(true)
       && MapImp_3385(Set_Collector_4276(pSet), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(1)))
         == MapConst_5_3385(true));
  requires 1 <= first_perm->val->mem_index && first_perm->val->mem_index <= n;
  requires Set_IsSubset_3385(WholeTidPermission(first_perm->val->t_id), Set_Add_3382(pSet, first_perm->val));
  modifies mem, r1, r2, pSet;



implementation Civl_CommutativityChecker_read_f_main_f_1(first_perm: One_4569, second_tid: Tid, second_sps: Set_4276)
   returns (first_Civl_PAs_read_f: [read_f]int, 
    first_Civl_PAs_main_s: [main_s]int, 
    second_Civl_PAs_read_f: [read_f]int)
{

  init:
    call first_Civl_PAs_read_f, first_Civl_PAs_main_s := read_f(first_perm);
    call second_Civl_PAs_read_f := main_f(second_tid, second_sps);
    assert true
       ==> (exists {:pool "K"} Civl_first_k#0: int, {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && Set_IsSubset_3385(WholeTidPermission(first_perm->val->t_id), pSet)
             && second_Civl_PAs_read_f
               == MapAdd_8791(MapConst_3_8802(0), 
                MapIte_8809_3((lambda second_pa: read_f :: 
                    1 <= second_pa->perm->val->mem_index
                       && second_pa->perm->val->mem_index <= n
                       && second_pa->perm->val->t_id == second_tid), 
                  MapConst_3_8802(1), 
                  MapConst_3_8802(0)))
             && first_Civl_PAs_read_f == MapConst_3_8802(0)
             && r1
               == old(r1)[first_perm->val->t_id := old(r1)[first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3382(old(pSet), first_perm->val)
             && first_Civl_PAs_main_s
               == MapAdd_8823(MapConst_3_8834(0), MapConst_3_8834(0)[main_s(first_perm->val->t_id) := 1])
             && mem == old(mem))
         || (exists {:pool "K"} Civl_first_k#0: int, {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && !Set_IsSubset_3385(WholeTidPermission(first_perm->val->t_id), pSet)
             && second_Civl_PAs_read_f
               == MapAdd_8791(MapConst_3_8802(0), 
                MapIte_8809_3((lambda second_pa: read_f :: 
                    1 <= second_pa->perm->val->mem_index
                       && second_pa->perm->val->mem_index <= n
                       && second_pa->perm->val->t_id == second_tid), 
                  MapConst_3_8802(1), 
                  MapConst_3_8802(0)))
             && first_Civl_PAs_read_f == MapConst_3_8802(0)
             && first_Civl_PAs_main_s == MapConst_3_8834(0)
             && r1
               == old(r1)[first_perm->val->t_id := old(r1)[first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3382(old(pSet), first_perm->val)
             && mem == old(mem))
         || (
          true
           && true
           && Set_IsSubset_3385(WholeTidPermission(first_perm->val->t_id), pSet)
           && second_Civl_PAs_read_f
             == MapAdd_8791(MapConst_3_8802(0), 
              MapIte_8809_3((lambda second_pa: read_f :: 
                  1 <= second_pa->perm->val->mem_index
                     && second_pa->perm->val->mem_index <= n
                     && second_pa->perm->val->t_id == second_tid), 
                MapConst_3_8802(1), 
                MapConst_3_8802(0)))
           && first_Civl_PAs_read_f == MapConst_3_8802(0)
           && r1
             == old(r1)[first_perm->val->t_id := old(r1)[first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet == Set_Add_3382(old(pSet), first_perm->val)
           && first_Civl_PAs_main_s
             == MapAdd_8823(MapConst_3_8834(0), MapConst_3_8834(0)[main_s(first_perm->val->t_id) := 1])
           && mem == old(mem))
         || (
          true
           && true
           && !Set_IsSubset_3385(WholeTidPermission(first_perm->val->t_id), pSet)
           && second_Civl_PAs_read_f
             == MapAdd_8791(MapConst_3_8802(0), 
              MapIte_8809_3((lambda second_pa: read_f :: 
                  1 <= second_pa->perm->val->mem_index
                     && second_pa->perm->val->mem_index <= n
                     && second_pa->perm->val->t_id == second_tid), 
                MapConst_3_8802(1), 
                MapConst_3_8802(0)))
           && first_Civl_PAs_read_f == MapConst_3_8802(0)
           && first_Civl_PAs_main_s == MapConst_3_8834(0)
           && r1
             == old(r1)[first_perm->val->t_id := old(r1)[first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet == Set_Add_3382(old(pSet), first_perm->val)
           && mem == old(mem));
    return;
}



procedure Civl_CommutativityChecker_read_f_main_f_1(first_perm: One_4569, second_tid: Tid, second_sps: Set_4276)
   returns (first_Civl_PAs_read_f: [read_f]int, 
    first_Civl_PAs_main_s: [main_s]int, 
    second_Civl_PAs_read_f: [read_f]int);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3385(One_Collector_4569(first_perm), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(0)))
         == MapConst_5_3385(true)
       && MapImp_3385(Set_Collector_4276(second_sps), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(1)))
         == MapConst_5_3385(true)
       && MapImp_3385(Set_Collector_4276(pSet), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(2)))
         == MapConst_5_3385(true));
  requires 1 <= first_perm->val->mem_index && first_perm->val->mem_index <= n;
  requires true
     ==> second_sps
       == Set_4276((lambda second_x: Permission :: 
          second_x->t_id == second_tid
             && 1 <= second_x->mem_index
             && second_x->mem_index <= n));
  requires Set_IsSubset_3385(WholeTidPermission(first_perm->val->t_id), Set_Add_3382(pSet, first_perm->val));
  modifies mem, r1, r2, pSet;



implementation Civl_CommutativityChecker_main_f_start_1(first_tid: Tid, first_sps: Set_4276, second_tid: Tid)
   returns (first_Civl_PAs_read_f: [read_f]int, second_Civl_PAs_main_f: [main_f]int)
{

  init:
    call first_Civl_PAs_read_f := main_f(first_tid, first_sps);
    call second_Civl_PAs_main_f := start(second_tid);
    assert true
       ==> true
         && pSet
           == Set_Difference_4276(old(pSet), 
            Set_4276((lambda second_x: Permission :: 
                second_x->t_id == second_tid
                   && 1 <= second_x->mem_index
                   && second_x->mem_index <= n)))
         && second_Civl_PAs_main_f
           == MapAdd_8759(MapConst_3_8770(0), 
            MapConst_3_8770(0)[main_f(second_tid, 
              Set_4276((lambda second_x: Permission :: 
                  second_x->t_id == second_tid
                     && 1 <= second_x->mem_index
                     && second_x->mem_index <= n))) := 1])
         && first_Civl_PAs_read_f
           == MapAdd_8791(MapConst_3_8802(0), 
            MapIte_8809_3((lambda first_pa: read_f :: 
                1 <= first_pa->perm->val->mem_index
                   && first_pa->perm->val->mem_index <= n
                   && first_pa->perm->val->t_id == first_tid), 
              MapConst_3_8802(1), 
              MapConst_3_8802(0)));
    return;
}



procedure Civl_CommutativityChecker_main_f_start_1(first_tid: Tid, first_sps: Set_4276, second_tid: Tid)
   returns (first_Civl_PAs_read_f: [read_f]int, second_Civl_PAs_main_f: [main_f]int);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3385(Set_Collector_4276(first_sps), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(0)))
         == MapConst_5_3385(true)
       && MapImp_3385(Set_Collector_4276(pSet), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(1)))
         == MapConst_5_3385(true));
  requires true
     ==> first_sps
       == Set_4276((lambda first_x: Permission :: 
          first_x->t_id == first_tid && 1 <= first_x->mem_index && first_x->mem_index <= n));
  requires Set_IsSubset_3385(Set_4276((lambda second_x: Permission :: 
        second_x->t_id == second_tid
           && 1 <= second_x->mem_index
           && second_x->mem_index <= n)), 
    pSet);
  requires false;
  modifies mem, r1, r2, pSet;



implementation Civl_GatePreservationChecker_start_main_f_1(first_tid: Tid, second_tid: Tid, second_sps: Set_4276)
   returns (first_Civl_PAs_main_f: [main_f]int, second_Civl_PAs_read_f: [read_f]int)
{

  init:
    call second_Civl_PAs_read_f := main_f(second_tid, second_sps);
    assert true
       ==> Set_IsSubset_3385(Set_4276((lambda first_x: Permission :: 
            first_x->t_id == first_tid && 1 <= first_x->mem_index && first_x->mem_index <= n)), 
        pSet);
    return;
}



procedure Civl_GatePreservationChecker_start_main_f_1(first_tid: Tid, second_tid: Tid, second_sps: Set_4276)
   returns (first_Civl_PAs_main_f: [main_f]int, second_Civl_PAs_read_f: [read_f]int);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3385(Set_Collector_4276(second_sps), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(0)))
         == MapConst_5_3385(true)
       && MapImp_3385(Set_Collector_4276(pSet), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(1)))
         == MapConst_5_3385(true));
  requires Set_IsSubset_3385(Set_4276((lambda first_x: Permission :: 
        first_x->t_id == first_tid && 1 <= first_x->mem_index && first_x->mem_index <= n)), 
    pSet);
  requires true
     ==> second_sps
       == Set_4276((lambda second_x: Permission :: 
          second_x->t_id == second_tid
             && 1 <= second_x->mem_index
             && second_x->mem_index <= n));
  requires false;
  modifies mem, r1, r2, pSet;



implementation Civl_CommutativityChecker_main_f_read_f_1(first_tid: Tid, first_sps: Set_4276, second_perm: One_4569)
   returns (first_Civl_PAs_read_f: [read_f]int, 
    second_Civl_PAs_read_f: [read_f]int, 
    second_Civl_PAs_main_s: [main_s]int)
{

  init:
    call first_Civl_PAs_read_f := main_f(first_tid, first_sps);
    call second_Civl_PAs_read_f, second_Civl_PAs_main_s := read_f(second_perm);
    assert true
       ==> (exists {:pool "K"} Civl_second_k#0: int, {:pool "V"} Civl_second_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_v(Civl_second_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && Set_IsSubset_3385(WholeTidPermission(second_perm->val->t_id), pSet)
             && true
             && second_Civl_PAs_read_f == MapConst_3_8802(0)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]]
             && pSet == Set_Add_3382(old(pSet), second_perm->val)
             && second_Civl_PAs_main_s
               == MapAdd_8823(MapConst_3_8834(0), MapConst_3_8834(0)[main_s(second_perm->val->t_id) := 1])
             && first_Civl_PAs_read_f
               == MapAdd_8791(MapConst_3_8802(0), 
                MapIte_8809_3((lambda first_pa: read_f :: 
                    1 <= first_pa->perm->val->mem_index
                       && first_pa->perm->val->mem_index <= n
                       && first_pa->perm->val->t_id == first_tid), 
                  MapConst_3_8802(1), 
                  MapConst_3_8802(0)))
             && mem == old(mem))
         || (exists {:pool "K"} Civl_second_k#0: int, {:pool "V"} Civl_second_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_v(Civl_second_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && !Set_IsSubset_3385(WholeTidPermission(second_perm->val->t_id), pSet)
             && true
             && second_Civl_PAs_read_f == MapConst_3_8802(0)
             && second_Civl_PAs_main_s == MapConst_3_8834(0)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]]
             && pSet == Set_Add_3382(old(pSet), second_perm->val)
             && first_Civl_PAs_read_f
               == MapAdd_8791(MapConst_3_8802(0), 
                MapIte_8809_3((lambda first_pa: read_f :: 
                    1 <= first_pa->perm->val->mem_index
                       && first_pa->perm->val->mem_index <= n
                       && first_pa->perm->val->t_id == first_tid), 
                  MapConst_3_8802(1), 
                  MapConst_3_8802(0)))
             && mem == old(mem))
         || (
          true
           && Set_IsSubset_3385(WholeTidPermission(second_perm->val->t_id), pSet)
           && true
           && second_Civl_PAs_read_f == MapConst_3_8802(0)
           && r1
             == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]]
           && pSet == Set_Add_3382(old(pSet), second_perm->val)
           && second_Civl_PAs_main_s
             == MapAdd_8823(MapConst_3_8834(0), MapConst_3_8834(0)[main_s(second_perm->val->t_id) := 1])
           && first_Civl_PAs_read_f
             == MapAdd_8791(MapConst_3_8802(0), 
              MapIte_8809_3((lambda first_pa: read_f :: 
                  1 <= first_pa->perm->val->mem_index
                     && first_pa->perm->val->mem_index <= n
                     && first_pa->perm->val->t_id == first_tid), 
                MapConst_3_8802(1), 
                MapConst_3_8802(0)))
           && mem == old(mem))
         || (
          true
           && !Set_IsSubset_3385(WholeTidPermission(second_perm->val->t_id), pSet)
           && true
           && second_Civl_PAs_read_f == MapConst_3_8802(0)
           && second_Civl_PAs_main_s == MapConst_3_8834(0)
           && r1
             == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]]
           && pSet == Set_Add_3382(old(pSet), second_perm->val)
           && first_Civl_PAs_read_f
             == MapAdd_8791(MapConst_3_8802(0), 
              MapIte_8809_3((lambda first_pa: read_f :: 
                  1 <= first_pa->perm->val->mem_index
                     && first_pa->perm->val->mem_index <= n
                     && first_pa->perm->val->t_id == first_tid), 
                MapConst_3_8802(1), 
                MapConst_3_8802(0)))
           && mem == old(mem));
    return;
}



procedure Civl_CommutativityChecker_main_f_read_f_1(first_tid: Tid, first_sps: Set_4276, second_perm: One_4569)
   returns (first_Civl_PAs_read_f: [read_f]int, 
    second_Civl_PAs_read_f: [read_f]int, 
    second_Civl_PAs_main_s: [main_s]int);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3385(Set_Collector_4276(first_sps), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(0)))
         == MapConst_5_3385(true)
       && MapImp_3385(One_Collector_4569(second_perm), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(1)))
         == MapConst_5_3385(true)
       && MapImp_3385(Set_Collector_4276(pSet), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(2)))
         == MapConst_5_3385(true));
  requires true
     ==> first_sps
       == Set_4276((lambda first_x: Permission :: 
          first_x->t_id == first_tid && 1 <= first_x->mem_index && first_x->mem_index <= n));
  requires 1 <= second_perm->val->mem_index && second_perm->val->mem_index <= n;
  requires false;
  modifies mem, r1, r2, pSet;



implementation Civl_CommutativityChecker_main_f_main_f_1(first_tid: Tid, first_sps: Set_4276, second_tid: Tid, second_sps: Set_4276)
   returns (first_Civl_PAs_read_f: [read_f]int, second_Civl_PAs_read_f: [read_f]int)
{

  init:
    call first_Civl_PAs_read_f := main_f(first_tid, first_sps);
    call second_Civl_PAs_read_f := main_f(second_tid, second_sps);
    assert true
       ==> true
         && true
         && second_Civl_PAs_read_f
           == MapAdd_8791(MapConst_3_8802(0), 
            MapIte_8809_3((lambda second_pa: read_f :: 
                1 <= second_pa->perm->val->mem_index
                   && second_pa->perm->val->mem_index <= n
                   && second_pa->perm->val->t_id == second_tid), 
              MapConst_3_8802(1), 
              MapConst_3_8802(0)))
         && first_Civl_PAs_read_f
           == MapAdd_8791(MapConst_3_8802(0), 
            MapIte_8809_3((lambda first_pa: read_f :: 
                1 <= first_pa->perm->val->mem_index
                   && first_pa->perm->val->mem_index <= n
                   && first_pa->perm->val->t_id == first_tid), 
              MapConst_3_8802(1), 
              MapConst_3_8802(0)))
         && pSet == old(pSet);
    return;
}



procedure Civl_CommutativityChecker_main_f_main_f_1(first_tid: Tid, first_sps: Set_4276, second_tid: Tid, second_sps: Set_4276)
   returns (first_Civl_PAs_read_f: [read_f]int, second_Civl_PAs_read_f: [read_f]int);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3385(Set_Collector_4276(first_sps), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(0)))
         == MapConst_5_3385(true)
       && MapImp_3385(Set_Collector_4276(second_sps), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(1)))
         == MapConst_5_3385(true)
       && MapImp_3385(Set_Collector_4276(pSet), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(2)))
         == MapConst_5_3385(true));
  requires true
     ==> first_sps
       == Set_4276((lambda first_x: Permission :: 
          first_x->t_id == first_tid && 1 <= first_x->mem_index && first_x->mem_index <= n));
  requires true
     ==> second_sps
       == Set_4276((lambda second_x: Permission :: 
          second_x->t_id == second_tid
             && 1 <= second_x->mem_index
             && second_x->mem_index <= n));
  requires false;
  modifies mem, r1, r2, pSet;



procedure Civl_PendingAsyncNoninterferenceChecker_read_f_1(perm: One_4569)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int);
  requires 1 <= perm->val->mem_index && perm->val->mem_index <= n;
  modifies mem, r1, r2, pSet;



implementation Civl_PendingAsyncNoninterferenceChecker_read_f_1(perm: One_4569)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int)
{
  var Civl_global_old_mem: [int]StampedValue;
  var Civl_global_old_r1: [Tid][int]StampedValue;
  var Civl_global_old_r2: [Tid][int]StampedValue;
  var Civl_global_old_pSet: Set_4276;
  var Civl_linear_Permission_available: [Permission]bool;

  init:
    Civl_global_old_mem, Civl_global_old_r1, Civl_global_old_r2, Civl_global_old_pSet := mem, r1, r2, pSet;
    Civl_linear_Permission_available := MapOr_4276(Set_Collector_4276(pSet), 
      MapOr_4276(One_Collector_4569(perm), MapConst_5_3385(false)));
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
  var Civl_global_old_pSet: Set_4276;
  var Civl_linear_Permission_available: [Permission]bool;

  init:
    Civl_global_old_mem, Civl_global_old_r1, Civl_global_old_r2, Civl_global_old_pSet := mem, r1, r2, pSet;
    Civl_linear_Permission_available := MapOr_4276(Set_Collector_4276(pSet), MapConst_5_3385(false));
    call main_s(tid);
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Permission_available, Civl_global_old_mem, Civl_global_old_r1, Civl_global_old_r2, Civl_global_old_pSet);
    return;
}



procedure Civl_PendingAsyncNoninterferenceChecker_main_f_1(tid: Tid, sps: Set_4276) returns (Civl_PAs_read_f: [read_f]int);
  requires true
     ==> sps
       == Set_4276((lambda x: Permission :: 
          x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
  modifies mem, r1, r2, pSet;



implementation Civl_PendingAsyncNoninterferenceChecker_main_f_1(tid: Tid, sps: Set_4276) returns (Civl_PAs_read_f: [read_f]int)
{
  var Civl_global_old_mem: [int]StampedValue;
  var Civl_global_old_r1: [Tid][int]StampedValue;
  var Civl_global_old_r2: [Tid][int]StampedValue;
  var Civl_global_old_pSet: Set_4276;
  var Civl_linear_Permission_available: [Permission]bool;

  init:
    Civl_global_old_mem, Civl_global_old_r1, Civl_global_old_r2, Civl_global_old_pSet := mem, r1, r2, pSet;
    Civl_linear_Permission_available := MapOr_4276(Set_Collector_4276(pSet), 
      MapOr_4276(Set_Collector_4276(sps), MapConst_5_3385(false)));
    call Civl_PAs_read_f := main_f(tid, sps);
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Permission_available, Civl_global_old_mem, Civl_global_old_r1, Civl_global_old_r2, Civl_global_old_pSet);
    return;
}



procedure {:inline 1} Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Permission_in: [Permission]bool, 
    Civl_global_old_mem: [int]StampedValue, 
    Civl_global_old_r1: [Tid][int]StampedValue, 
    Civl_global_old_r2: [Tid][int]StampedValue, 
    Civl_global_old_pSet: Set_4276);



implementation Civl_Wrapper_NoninterferenceChecker_1(Civl_Civl_linear_Permission_in: [Permission]bool, 
    Civl_Civl_global_old_mem: [int]StampedValue, 
    Civl_Civl_global_old_r1: [Tid][int]StampedValue, 
    Civl_Civl_global_old_r2: [Tid][int]StampedValue, 
    Civl_Civl_global_old_pSet: Set_4276)
{

  enter:
    return;
}



implementation Civl_LinearityChecker_start(tid: Tid) returns (Civl_PAs_main_f: [main_f]int)
{
  var Civl_pa1_main_f: main_f;
  var Civl_pa2_main_f: main_f;

  init:
    call Civl_PAs_main_f := start(tid);
    goto Permission_out_of_thin_air_main_f, Permission_duplication_main_f, Permission_duplication_main_f_main_f;

  Permission_out_of_thin_air_main_f:
    assume Civl_pa1_main_f is main_f && Civl_PAs_main_f[Civl_pa1_main_f] >= 1;
    assert MapImp_3385(MapOr_4276(Set_Collector_4276(Civl_pa1_main_f->sps), MapConst_5_3385(false)), 
        old(MapOr_4276(Set_Collector_4276(pSet), MapConst_5_3385(false))))
       == MapConst_5_3385(true);
    return;

  Permission_duplication_main_f:
    assume Civl_pa1_main_f is main_f && Civl_PAs_main_f[Civl_pa1_main_f] >= 1;
    assert MapAnd_4276(MapOr_4276(Set_Collector_4276(pSet), MapConst_5_3385(false)), 
        MapOr_4276(Set_Collector_4276(Civl_pa1_main_f->sps), MapConst_5_3385(false)))
       == MapConst_5_3385(false);
    return;

  Permission_duplication_main_f_main_f:
    assume Civl_pa1_main_f != Civl_pa2_main_f
       && 
      Civl_pa1_main_f is main_f
       && Civl_pa2_main_f is main_f
       && 
      Civl_PAs_main_f[Civl_pa1_main_f] >= 1
       && Civl_PAs_main_f[Civl_pa2_main_f] >= 1;
    assert MapAnd_4276(MapOr_4276(Set_Collector_4276(Civl_pa1_main_f->sps), MapConst_5_3385(false)), 
        MapOr_4276(Set_Collector_4276(Civl_pa2_main_f->sps), MapConst_5_3385(false)))
       == MapConst_5_3385(false);
    return;
}



procedure Civl_LinearityChecker_start(tid: Tid) returns (Civl_PAs_main_f: [main_f]int);
  requires Set_IsSubset_3385(Set_4276((lambda x: Permission :: 
        x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n)), 
    pSet);
  requires true;
  modifies pSet;



implementation Civl_LinearityChecker_read_f(perm: One_4569)
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
    assert MapImp_3385(MapOr_4276(One_Collector_4569(Civl_pa1_read_f->perm), MapConst_5_3385(false)), 
        old(MapOr_4276(Set_Collector_4276(pSet), 
          MapOr_4276(One_Collector_4569(perm), MapConst_5_3385(false)))))
       == MapConst_5_3385(true);
    return;

  Permission_duplication_read_f:
    assume Civl_pa1_read_f is read_f && Civl_PAs_read_f[Civl_pa1_read_f] >= 1;
    assert MapAnd_4276(MapOr_4276(Set_Collector_4276(pSet), MapConst_5_3385(false)), 
        MapOr_4276(One_Collector_4569(Civl_pa1_read_f->perm), MapConst_5_3385(false)))
       == MapConst_5_3385(false);
    return;

  Permission_duplication_read_f_read_f:
    assume Civl_pa1_read_f != Civl_pa2_read_f
       && 
      Civl_pa1_read_f is read_f
       && Civl_pa2_read_f is read_f
       && 
      Civl_PAs_read_f[Civl_pa1_read_f] >= 1
       && Civl_PAs_read_f[Civl_pa2_read_f] >= 1;
    assert MapAnd_4276(MapOr_4276(One_Collector_4569(Civl_pa1_read_f->perm), MapConst_5_3385(false)), 
        MapOr_4276(One_Collector_4569(Civl_pa2_read_f->perm), MapConst_5_3385(false)))
       == MapConst_5_3385(false);
    return;
}



procedure Civl_LinearityChecker_read_f(perm: One_4569)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int);
  requires 1 <= perm->val->mem_index && perm->val->mem_index <= n;
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3385(One_Collector_4569(perm), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(0)))
         == MapConst_5_3385(true)
       && MapImp_3385(Set_Collector_4276(pSet), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(1)))
         == MapConst_5_3385(true));
  modifies r1, pSet;



implementation Civl_LinearityChecker_main_f(tid: Tid, sps: Set_4276) returns (Civl_PAs_read_f: [read_f]int)
{
  var Civl_pa1_read_f: read_f;
  var Civl_pa2_read_f: read_f;

  init:
    call Civl_PAs_read_f := main_f(tid, sps);
    goto Permission_out_of_thin_air_read_f, Permission_duplication_read_f, Permission_duplication_read_f_read_f;

  Permission_out_of_thin_air_read_f:
    assume Civl_pa1_read_f is read_f && Civl_PAs_read_f[Civl_pa1_read_f] >= 1;
    assert MapImp_3385(MapOr_4276(One_Collector_4569(Civl_pa1_read_f->perm), MapConst_5_3385(false)), 
        old(MapOr_4276(Set_Collector_4276(pSet), 
          MapOr_4276(Set_Collector_4276(sps), MapConst_5_3385(false)))))
       == MapConst_5_3385(true);
    return;

  Permission_duplication_read_f:
    assume Civl_pa1_read_f is read_f && Civl_PAs_read_f[Civl_pa1_read_f] >= 1;
    assert MapAnd_4276(MapOr_4276(Set_Collector_4276(pSet), MapConst_5_3385(false)), 
        MapOr_4276(One_Collector_4569(Civl_pa1_read_f->perm), MapConst_5_3385(false)))
       == MapConst_5_3385(false);
    return;

  Permission_duplication_read_f_read_f:
    assume Civl_pa1_read_f != Civl_pa2_read_f
       && 
      Civl_pa1_read_f is read_f
       && Civl_pa2_read_f is read_f
       && 
      Civl_PAs_read_f[Civl_pa1_read_f] >= 1
       && Civl_PAs_read_f[Civl_pa2_read_f] >= 1;
    assert MapAnd_4276(MapOr_4276(One_Collector_4569(Civl_pa1_read_f->perm), MapConst_5_3385(false)), 
        MapOr_4276(One_Collector_4569(Civl_pa2_read_f->perm), MapConst_5_3385(false)))
       == MapConst_5_3385(false);
    return;
}



procedure Civl_LinearityChecker_main_f(tid: Tid, sps: Set_4276) returns (Civl_PAs_read_f: [read_f]int);
  requires true
     ==> sps
       == Set_4276((lambda x: Permission :: 
          x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3385(Set_Collector_4276(sps), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(0)))
         == MapConst_5_3385(true)
       && MapImp_3385(Set_Collector_4276(pSet), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(1)))
         == MapConst_5_3385(true));
  modifies pSet;



procedure Civl_PartitionChecker_main_f(tid: Tid, sps: Set_4276) returns (Civl_PAs_read_f: [read_f]int);
  modifies pSet;



implementation Civl_PartitionChecker_main_f(tid: Tid, sps: Set_4276) returns (Civl_PAs_read_f: [read_f]int)
{
  var Civl_local_Civl_PAs_read_f: read_f;

  Civl_PartitionChecker_main_f:
    call Civl_PAs_read_f := main_f(tid, sps);
    assert Civl_PAs_read_f != MapConst_3_8802(0) ==> true;
    goto label_Civl_PAs_read_f;

  label_Civl_PAs_read_f:
    assume Civl_PAs_read_f[Civl_local_Civl_PAs_read_f] >= 1;
    assert 1 <= Civl_local_Civl_PAs_read_f->perm->val->mem_index
       && Civl_local_Civl_PAs_read_f->perm->val->mem_index <= n;
    return;
}



procedure Civl_PartitionChecker_read_f(perm: One_4569)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int);
  modifies r1, pSet;



implementation Civl_PartitionChecker_read_f(perm: One_4569)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int)
{
  var Civl_local_Civl_PAs_read_f: read_f;

  Civl_PartitionChecker_read_f:
    call Civl_PAs_read_f, Civl_PAs_main_s := read_f(perm);
    assert Civl_PAs_read_f != MapConst_3_8802(0) ==> Civl_PAs_main_s == MapConst_3_8834(0);
    goto label_Civl_PAs_read_f;

  label_Civl_PAs_read_f:
    assume Civl_PAs_read_f[Civl_local_Civl_PAs_read_f] >= 1;
    assert 1 <= Civl_local_Civl_PAs_read_f->perm->val->mem_index
       && Civl_local_Civl_PAs_read_f->perm->val->mem_index <= n;
    return;
}



procedure Civl_ISR_base_main_f(tid: Tid, sps: Set_4276)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int);
  requires (forall j: int :: 
    0 <= j && j <= n
       ==> (forall r1: [Tid][int]StampedValue :: 
        (forall i: int :: 
            1 <= i && i <= j ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i])
           ==> 
          true
           ==> Set_IsSubset_3385(Set_4276((lambda {:pool "D"} x: Permission :: 
                x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j)), 
            sps)));
  requires sps == WholeTidPermission(tid);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3385(Set_Collector_4276(sps), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(0)))
         == MapConst_5_3385(true)
       && MapImp_3385(Set_Collector_4276(pSet), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(1)))
         == MapConst_5_3385(true));
  modifies r1, pSet;



implementation Civl_ISR_base_main_f(tid: Tid, sps: Set_4276)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int)
{

  ISR_base_main_f:
    assert true
       ==> sps
         == Set_4276((lambda x: Permission :: 
            x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
    call Civl_PAs_read_f := main_f(tid, sps);
    Civl_PAs_main_s := MapConst_3_8834(0);
    assert (exists {:pool "A"} Civl_j#0: int :: 
        0 <= Civl_j#0
           && Civl_j#0 <= n
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0 ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i])
           && true
           && Civl_j#0 < n
           && true
           && Civl_PAs_main_s == MapConst_3_8834(0)
           && pSet
             == Set_Union_4276(old(pSet), 
              Set_4276((lambda {:pool "D"} x: Permission :: 
                  x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
           && Civl_PAs_read_f
             == MapAdd_8791(MapConst_3_8802(0), 
              MapIte_8809_3((lambda {:pool "C"} pa: read_f :: 
                  Civl_j#0 + 1 <= pa->perm->val->mem_index
                     && pa->perm->val->mem_index <= n
                     && pa->perm->val->t_id == tid), 
                MapConst_3_8802(1), 
                MapConst_3_8802(0))))
       || (exists {:pool "A"} Civl_j#0: int :: 
        0 <= Civl_j#0
           && Civl_j#0 <= n
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0 ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i])
           && true
           && n <= Civl_j#0
           && Civl_PAs_read_f == MapConst_3_8802(0)
           && pSet
             == Set_Union_4276(old(pSet), 
              Set_4276((lambda {:pool "D"} x: Permission :: 
                  x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
           && Civl_PAs_main_s
             == MapAdd_8823(MapConst_3_8834(0), MapConst_3_8834(0)[main_s(tid) := 1]));
    return;
}



procedure Civl_ISR_conclusion_main_f(tid: Tid, sps: Set_4276)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int);
  requires true
     ==> (forall r1: [Tid][int]StampedValue :: 
      (forall i: int :: 
          1 <= i && i <= n ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i])
         ==> Set_IsSubset_3385(Set_4276((lambda x: Permission :: 
              x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n)), 
          sps));
  requires true
     ==> sps
       == Set_4276((lambda x: Permission :: 
          x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3385(Set_Collector_4276(sps), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(0)))
         == MapConst_5_3385(true)
       && MapImp_3385(Set_Collector_4276(pSet), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(1)))
         == MapConst_5_3385(true));
  modifies r1, pSet;



implementation Civl_ISR_conclusion_main_f(tid: Tid, sps: Set_4276)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int)
{

  ISR_conclusion_main_f:
    assert (forall j: int :: 
      0 <= j && j <= n
         ==> (forall r1: [Tid][int]StampedValue :: 
          (forall i: int :: 
              1 <= i && i <= j ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i])
             ==> 
            true
             ==> Set_IsSubset_3385(Set_4276((lambda {:pool "D"} x: Permission :: 
                  x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j)), 
              sps)));
    assert sps == WholeTidPermission(tid);
    call Civl_PAs_read_f, Civl_PAs_main_s := Inv_f(tid, sps);
    assume Civl_PAs_read_f == MapConst_3_8802(0);
    assert true
       && (forall i: int :: 
        1 <= i && i <= n ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i])
       && pSet
         == Set_Union_4276(old(pSet), 
          Set_4276((lambda x: Permission :: 
              x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n)))
       && Civl_PAs_main_s
         == MapAdd_8823(MapConst_3_8834(0), MapConst_3_8834(0)[main_s(tid) := 1])
       && mem == old(mem)
       && r2 == old(r2);
    return;
}



procedure Civl_ISR_step_Inv_f_read_f(tid: Tid, sps: Set_4276)
   returns (Civl_PAs_read_f: [read_f]int, 
    Civl_PAs_main_s: [main_s]int, 
    Civl_choice: Choice_Inv_f);
  requires (forall j: int :: 
    0 <= j && j <= n
       ==> (forall r1: [Tid][int]StampedValue :: 
        (forall i: int :: 
            1 <= i && i <= j ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i])
           ==> 
          true
           ==> Set_IsSubset_3385(Set_4276((lambda {:pool "D"} x: Permission :: 
                x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j)), 
            sps)));
  requires sps == WholeTidPermission(tid);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3385(Set_Collector_4276(sps), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(0)))
         == MapConst_5_3385(true)
       && MapImp_3385(Set_Collector_4276(pSet), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(1)))
         == MapConst_5_3385(true));
  modifies r1, pSet;



implementation Civl_ISR_step_Inv_f_read_f(tid: Tid, sps: Set_4276)
   returns (Civl_PAs_read_f: [read_f]int, 
    Civl_PAs_main_s: [main_s]int, 
    Civl_choice: Choice_Inv_f)
{
  var Civl_newPAs_read_f: [read_f]int;
  var Civl_newPAs_main_s: [main_s]int;

  ISR_step_Inv_f_read_f:
    call Civl_PAs_read_f, Civl_PAs_main_s, Civl_choice := Inv_f_With_Choice(tid, sps);
    assume Civl_choice is Choice_Inv_f_read_f;
    assume Civl_PAs_read_f[Civl_choice->read_f] > 0;
    Civl_PAs_read_f[Civl_choice->read_f] := Civl_PAs_read_f[Civl_choice->read_f] - 1;
    assert 1 <= Civl_choice->read_f->perm->val->mem_index
       && Civl_choice->read_f->perm->val->mem_index <= n;
    call Civl_newPAs_read_f, Civl_newPAs_main_s := read_f(Civl_choice->read_f->perm);
    Civl_PAs_read_f, Civl_PAs_main_s := MapAdd_8791(Civl_PAs_read_f, Civl_newPAs_read_f), MapAdd_8823(Civl_PAs_main_s, Civl_newPAs_main_s);
    assert (exists {:pool "A"} Civl_j#0: int :: 
        0 <= Civl_j#0
           && Civl_j#0 <= n
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0 ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i])
           && true
           && Civl_j#0 < n
           && true
           && Civl_PAs_main_s == MapConst_3_8834(0)
           && pSet
             == Set_Union_4276(old(pSet), 
              Set_4276((lambda {:pool "D"} x: Permission :: 
                  x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
           && Civl_PAs_read_f
             == MapAdd_8791(MapConst_3_8802(0), 
              MapIte_8809_3((lambda {:pool "C"} pa: read_f :: 
                  Civl_j#0 + 1 <= pa->perm->val->mem_index
                     && pa->perm->val->mem_index <= n
                     && pa->perm->val->t_id == tid), 
                MapConst_3_8802(1), 
                MapConst_3_8802(0))))
       || (exists {:pool "A"} Civl_j#0: int :: 
        0 <= Civl_j#0
           && Civl_j#0 <= n
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0 ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i])
           && true
           && n <= Civl_j#0
           && Civl_PAs_read_f == MapConst_3_8802(0)
           && pSet
             == Set_Union_4276(old(pSet), 
              Set_4276((lambda {:pool "D"} x: Permission :: 
                  x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
           && Civl_PAs_main_s
             == MapAdd_8823(MapConst_3_8834(0), MapConst_3_8834(0)[main_s(tid) := 1]));
    return;
}



procedure Civl_ISR_SideCondition_main_f(tid: Tid, sps: Set_4276) returns (Civl_PAs_read_f: [read_f]int);
  requires true
     ==> sps
       == Set_4276((lambda x: Permission :: 
          x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3385(Set_Collector_4276(sps), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(0)))
         == MapConst_5_3385(true)
       && MapImp_3385(Set_Collector_4276(pSet), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(1)))
         == MapConst_5_3385(true));
  modifies pSet;



implementation Civl_ISR_SideCondition_main_f(tid: Tid, sps: Set_4276) returns (Civl_PAs_read_f: [read_f]int)
{

  init:
    call Civl_PAs_read_f := main_f(tid, sps);
    goto Permission_only_put_perm_main_f;

  Permission_only_put_perm_main_f:
    assume true;
    assert MapImp_3385(old(MapOr_4276(Set_Collector_4276(pSet), MapConst_5_3385(false))), 
        MapOr_4276(Set_Collector_4276(pSet), MapConst_5_3385(false)))
       == MapConst_5_3385(true);
    return;
}



procedure Civl_ISR_AllPendingAsyncsInElim_read_f(perm: One_4569)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int);
  modifies r1, pSet;



implementation Civl_ISR_AllPendingAsyncsInElim_read_f(perm: One_4569)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int)
{

  ISR_AllPendingAsyncsInElim_read_f:
    assume !Set_IsSubset_3385(WholeTidPermission(perm->val->t_id), Set_Add_3382(pSet, perm->val));
    call Civl_PAs_read_f, Civl_PAs_main_s := read_f(perm);
    assert Civl_PAs_main_s == MapConst_3_8834(0);
    return;
}



procedure Civl_ISR_AllPendingAsyncsNotInElim_read_f(perm: One_4569)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int);
  modifies r1, pSet;



implementation Civl_ISR_AllPendingAsyncsNotInElim_read_f(perm: One_4569)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int)
{

  ISR_AllPendingAsyncsNotInElim_read_f:
    assume Set_IsSubset_3385(WholeTidPermission(perm->val->t_id), Set_Add_3382(pSet, perm->val));
    call Civl_PAs_read_f, Civl_PAs_main_s := read_f(perm);
    assert Civl_PAs_read_f == MapConst_3_8802(0);
    return;
}



procedure Civl_ISR_SideCondition_read_f(perm: One_4569)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int);
  requires 1 <= perm->val->mem_index && perm->val->mem_index <= n;
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3385(One_Collector_4569(perm), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(0)))
         == MapConst_5_3385(true)
       && MapImp_3385(Set_Collector_4276(pSet), 
          MapEq_4276_3(Civl_partition_Permission, MapConst_3_4276(1)))
         == MapConst_5_3385(true));
  modifies r1, pSet;



implementation Civl_ISR_SideCondition_read_f(perm: One_4569)
   returns (Civl_PAs_read_f: [read_f]int, Civl_PAs_main_s: [main_s]int)
{

  init:
    call Civl_PAs_read_f, Civl_PAs_main_s := read_f(perm);
    goto Permission_only_put_perm_read_f;

  Permission_only_put_perm_read_f:
    assume true;
    assert MapImp_3385(old(MapOr_4276(Set_Collector_4276(pSet), MapConst_5_3385(false))), 
        MapOr_4276(Set_Collector_4276(pSet), MapConst_5_3385(false)))
       == MapConst_5_3385(true);
    return;
}



procedure Civl_ISR_InconsistencyChecker_main_f_read_f_read_f();
  modifies r1, pSet;



implementation Civl_ISR_InconsistencyChecker_main_f_read_f_read_f()
{
  var Civl_E1_read_f: read_f;
  var Civl_E2_read_f: read_f;
  var Civl_tempg_mem: [int]StampedValue;
  var Civl_tempg_r1: [Tid][int]StampedValue;
  var Civl_tempg_r2: [Tid][int]StampedValue;
  var Civl_tempg_pSet: Set_4276;
  var Civl_templ_tid: Tid;
  var Civl_templ_sps: Set_4276;

  ISR_InconsistencyChecker_main_f_read_f_read_f:
    assume (true
         ==> Civl_templ_sps
           == Set_4276((lambda x: Permission :: 
              x->t_id == Civl_templ_tid && 1 <= x->mem_index && x->mem_index <= n)))
       && true;
    assume MapAnd_4276(MapOr_4276(Set_Collector_4276(pSet), MapConst_5_3385(false)), 
          MapOr_4276(One_Collector_4569(Civl_E1_read_f->perm), MapConst_5_3385(false)))
         == MapConst_5_3385(false)
       && MapAnd_4276(MapOr_4276(Set_Collector_4276(pSet), MapConst_5_3385(false)), 
          MapOr_4276(One_Collector_4569(Civl_E2_read_f->perm), MapConst_5_3385(false)))
         == MapConst_5_3385(false)
       && MapAnd_4276(MapOr_4276(One_Collector_4569(Civl_E1_read_f->perm), MapConst_5_3385(false)), 
          MapOr_4276(One_Collector_4569(Civl_E2_read_f->perm), MapConst_5_3385(false)))
         == MapConst_5_3385(false);
    assume MapImp_3385(MapOr_4276(One_Collector_4569(Civl_E1_read_f->perm), MapConst_5_3385(false)), 
          MapOr_4276(Set_Collector_4276(Civl_templ_sps), MapConst_5_3385(false)))
         == MapConst_5_3385(true)
       && MapImp_3385(MapOr_4276(One_Collector_4569(Civl_E2_read_f->perm), MapConst_5_3385(false)), 
          MapOr_4276(Set_Collector_4276(Civl_templ_sps), MapConst_5_3385(false)))
         == MapConst_5_3385(true);
    assert !(
      1 <= Civl_E1_read_f->perm->val->mem_index
       && Civl_E1_read_f->perm->val->mem_index <= n
       && 
      Set_IsSubset_3385(WholeTidPermission(Civl_E2_read_f->perm->val->t_id), 
        Set_Add_3382(pSet, Civl_E2_read_f->perm->val))
       && 
      1 <= Civl_E2_read_f->perm->val->mem_index
       && Civl_E2_read_f->perm->val->mem_index <= n);
    return;
}


