// Boogie program verifier version 3.1.6.0, Copyright (c) 2003-2014, Microsoft.
// Command Line Options: snapshot-scatter-gather-namratha2.bpl /civlDesugaredFile:namsugar.bpl

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

var pSet: Set_4166;

var done_first: [Tid]bool;

var done_second: [Tid]bool;

function {:inline} WholeTidPermission(tid: Tid) : Set_4166
{
  Set_4166((lambda {:pool "D"} x: Permission :: 
      x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n))
}

datatype action_main_f {
  action_main_f(tid: Tid, sps: Set_4166)
}

datatype main_f' {
  main_f'(tid: Tid, sps: Set_4166)
}

datatype read_f {
  read_f(perm: One_4378)
}

const Identity: [int]int;

function {:inline} AtLeast(x: int) : [int]bool
{
  MapLe_1222(MapConst_1239_1222(x), Identity)
}

function {:inline} Range(from: int, n: int) : [int]bool
{
  MapDiff_1242(AtLeast(from), AtLeast(from + n))
}

type {:builtin "Seq"} Seq _;

pure procedure Assume(b: bool);
  ensures b;



datatype Set_4166 {
  Set_4166(val: [Permission]bool)
}

datatype One_4378 {
  One_4378(val: Permission)
}

procedure create_asyncs_3324(PAs: [read_f]bool);



pure procedure Set_Put_3301(path: Set_4166, l: Set_4166);



function {:inline} Set_Add_3301(a: Set_4166, t: Permission) : Set_4166
{
  Set_4166(a->val[t := true])
}

function {:inline} Set_IsSubset_3308(a: Set_4166, b: Set_4166) : bool
{
  IsSubset_3308(a->val, b->val)
}

function {:inline} IsSubset_3308(a: [Permission]bool, b: [Permission]bool) : bool
{
  MapImp_3308(a, b) == MapConst_5_3308(true)
}

function {:builtin "MapImp"} MapImp_3308([Permission]bool, [Permission]bool) : [Permission]bool;

function {:builtin "MapConst"} MapConst_5_3308(bool) : [Permission]bool;

pure procedure One_Put_3301(path: Set_4166, l: One_4378);



pure procedure Set_Get_3352(path: Set_4166, k: [Permission]bool) returns (l: Set_4166);



procedure set_choice_3356(choice: read_f);



function {:builtin "MapConst"} MapConst_1239_1222(int) : [int]int;

function {:builtin "MapLe"} MapLe_1222([int]int, [int]int) : [int]bool;

function {:inline} MapDiff_1242(a: [int]bool, b: [int]bool) : [int]bool
{
  MapAnd_1242(a, MapNot_1242(b))
}

function {:builtin "MapNot"} MapNot_1242([int]bool) : [int]bool;

function {:builtin "MapAnd"} MapAnd_1242([int]bool, [int]bool) : [int]bool;

datatype Vec_5 {
  Vec_5(contents: [int]bool, len: int)
}

function Default_5() : bool;

function {:builtin "MapConst"} MapConst_5_1263(bool) : [int]bool;

function {:builtin "MapIte"} MapIte_1263_5([int]bool, [int]bool, [int]bool) : [int]bool;

datatype Vec_1239 {
  Vec_1239(contents: [int]int, len: int)
}

function Default_1239() : int;

function {:builtin "MapIte"} MapIte_1263_1239([int]bool, [int]int, [int]int) : [int]int;

function {:inline} Set_Empty_4166() : Set_4166
{
  Set_4166(MapConst_5_3308(false))
}

function Set_Size_4166(a: Set_4166) : int;

function {:inline} Set_Contains_4166(a: Set_4166, t: Permission) : bool
{
  a->val[t]
}

function {:inline} Set_Remove_4166(a: Set_4166, t: Permission) : Set_4166
{
  Set_4166(a->val[t := false])
}

function {:inline} Set_Difference_4166(a: Set_4166, b: Set_4166) : Set_4166
{
  Set_4166(MapDiff_4166(a->val, b->val))
}

function {:inline} MapDiff_4166(a: [Permission]bool, b: [Permission]bool) : [Permission]bool
{
  MapAnd_4166(a, MapNot_4166(b))
}

function {:builtin "MapNot"} MapNot_4166([Permission]bool) : [Permission]bool;

function {:builtin "MapAnd"} MapAnd_4166([Permission]bool, [Permission]bool) : [Permission]bool;

function {:inline} Set_Intersection_4166(a: Set_4166, b: Set_4166) : Set_4166
{
  Set_4166(MapAnd_4166(a->val, b->val))
}

function {:inline} Set_Union_4166(a: Set_4166, b: Set_4166) : Set_4166
{
  Set_4166(MapOr_4166(a->val, b->val))
}

function {:builtin "MapOr"} MapOr_4166([Permission]bool, [Permission]bool) : [Permission]bool;

function Choice_3308(a: [Permission]bool) : Permission;

function Choice_1222(a: [int]bool) : int;

axiom n >= 1;

axiom (forall x: int :: Identity[x] == x);

axiom (forall x: Vec_1239 :: 
  { x->len } { x->contents } 
  MapIte_1263_1239(Range(0, x->len), MapConst_1239_1222(Default_1239()), x->contents)
     == MapConst_1239_1222(Default_1239()));

axiom (forall x: Vec_5 :: 
  { x->len } { x->contents } 
  MapIte_1263_5(Range(0, x->len), MapConst_5_1263(Default_5()), x->contents)
     == MapConst_5_1263(Default_5()));

axiom (forall x: Vec_1239 :: { x->len } x->len >= 0);

axiom (forall x: Vec_5 :: { x->len } x->len >= 0);

axiom (forall a: Set_4166 :: a == Set_Empty_4166() || 0 < Set_Size_4166(a));

axiom Set_Size_4166(Set_Empty_4166()) == 0;

axiom (forall a: Set_4166, t: Permission :: 
  { Set_Add_3301(a, t) } 
  Set_Size_4166(Set_Add_3301(a, t))
     == (if Set_Contains_4166(a, t) then Set_Size_4166(a) else Set_Size_4166(a) + 1));

axiom (forall a: Set_4166, t: Permission :: 
  { Set_Remove_4166(a, t) } 
  Set_Size_4166(Set_Remove_4166(a, t))
     == (if Set_Contains_4166(a, t) then Set_Size_4166(a) - 1 else Set_Size_4166(a)));

axiom (forall a: Set_4166, b: Set_4166 :: 
  { Set_Difference_4166(a, b) } 
    { Set_Intersection_4166(a, b) } 
    { Set_Union_4166(a, b) } 
  Set_Size_4166(a)
     == Set_Size_4166(Set_Difference_4166(a, b))
       + Set_Size_4166(Set_Intersection_4166(a, b)));

axiom (forall a: Set_4166, b: Set_4166 :: 
  { Set_Union_4166(a, b) } { Set_Intersection_4166(a, b) } 
  Set_Size_4166(Set_Union_4166(a, b)) + Set_Size_4166(Set_Intersection_4166(a, b))
     == Set_Size_4166(a) + Set_Size_4166(b));

axiom (forall a: [int]bool :: 
  { Choice_1222(a) } 
  a == MapConst_5_1263(false) || a[Choice_1222(a)]);

axiom (forall a: [Permission]bool :: 
  { Choice_3308(a) } 
  a == MapConst_5_3308(false) || a[Choice_3308(a)]);

function {:builtin "MapConst"} MapConst_3_4166(int) : [Permission]int;

function {:builtin "MapEq"} MapEq_4166_3([Permission]int, [Permission]int) : [Permission]bool;

function {:builtin "MapAdd"} MapAdd_4166([Permission]int, [Permission]int) : [Permission]int;

function {:builtin "MapIte"} MapIte_4166_3([Permission]bool, [Permission]int, [Permission]int) : [Permission]int;

function {:builtin "MapLe"} MapLe_4166([Permission]int, [Permission]int) : [Permission]bool;

function {:inline} Set_Collector_4166(a: Set_4166) : [Permission]bool
{
  a->val
}

function {:inline} One_Collector_4378(a: One_4378) : [Permission]bool
{
  MapOne_4378(a->val)
}

function {:inline} MapOne_4378(t: Permission) : [Permission]bool
{
  MapConst_5_3308(false)[t := true]
}

function {:inline} Collector_read_f_Permission(target: read_f) : [Permission]bool
{
  (if target is read_f
     then MapOr_4166(One_Collector_4378(target->perm), MapConst_5_3308(false))
     else MapConst_5_3308(false))
}

function {:builtin "MapAdd"} MapAdd_8239([action_main_f]int, [action_main_f]int) : [action_main_f]int;

function {:builtin "MapConst"} MapConst_3_8250(int) : [action_main_f]int;

function {:builtin "MapIte"} MapIte_8257_3([action_main_f]bool, [action_main_f]int, [action_main_f]int)
   : [action_main_f]int;

function {:builtin "MapAdd"} MapAdd_8271([main_f']int, [main_f']int) : [main_f']int;

function {:builtin "MapConst"} MapConst_3_8282(int) : [main_f']int;

function {:builtin "MapIte"} MapIte_8289_3([main_f']bool, [main_f']int, [main_f']int) : [main_f']int;

function {:builtin "MapAdd"} MapAdd_8303([read_f]int, [read_f]int) : [read_f]int;

function {:builtin "MapConst"} MapConst_3_8314(int) : [read_f]int;

function {:builtin "MapIte"} MapIte_8321_3([read_f]bool, [read_f]int, [read_f]int) : [read_f]int;

datatype Choice_Inv_f {
  Choice_Inv_f_read_f(read_f: read_f)
}

function Trigger_write_x(x: StampedValue) : bool;

function Trigger_main_f'_snapshot(snapshot: [int]StampedValue) : bool;

function Trigger_read_f_k(k: int) : bool;

function Trigger_read_f_v(v: Value) : bool;

function Trigger_Inv_f_j(j: int) : bool;

function Trigger_Inv_f_sps2(sps2: Set_4166) : bool;

function Trigger_Inv_f_done_set(done_set: Set_4166) : bool;

function Trigger_Inv_f_choice(choice: read_f) : bool;

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
      Civl_old_pSet: Set_4166, 
      Civl_old_done_first: [Tid]bool, 
      Civl_old_done_second: [Tid]bool, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4166, 
      Civl_done_first: [Tid]bool, 
      Civl_done_second: [Tid]bool :: 
    Civl_mem == Civl_old_mem[i := StampedValue(Civl_old_mem[i]->ts + 1, v)])
}

implementation main_f'(tid: Tid, sps: Set_4166)
{
  var snapshot: [int]StampedValue;

  /*** structured program:
    assume {:add_to_pool "A", 0, n} true;
    assert sps == WholeTidPermission(tid);
    assert done_first[tid] <==> false;
    assume (forall i: int :: 
      1 <= i && i <= n ==> snapshot[i]->ts < mem[i]->ts || snapshot[i] == mem[i]);
    call Set_Put_3301(pSet, sps);
    done_first[tid] := true;
  **** end structured program */

  anon0:
    assume Trigger_main_f'_snapshot(snapshot);
    assume {:add_to_pool "A", 0, n} true;
    assume (forall i: int :: 
      1 <= i && i <= n ==> snapshot[i]->ts < mem[i]->ts || snapshot[i] == mem[i]);
    pSet := Set_Union_4166(pSet, sps);
    done_first[tid] := true;
    return;
}



procedure {:inline 1} main_f'(tid: Tid, sps: Set_4166);
  modifies pSet, done_first;



function {:inline} Civl_InputOutputRelation_main_f'(tid: Tid, sps: Set_4166) : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_r1: [Tid][int]StampedValue, 
      Civl_old_r2: [Tid][int]StampedValue, 
      Civl_old_pSet: Set_4166, 
      Civl_old_done_first: [Tid]bool, 
      Civl_old_done_second: [Tid]bool, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4166, 
      Civl_done_first: [Tid]bool, 
      Civl_done_second: [Tid]bool :: 
    (true ==> (Civl_old_done_first[tid] <==> false))
       && (true ==> sps == WholeTidPermission(tid))
       && (exists Civl_snapshot#0: [int]StampedValue :: 
        true
           && (forall i: int :: 
            1 <= i && i <= n
               ==> Civl_snapshot#0[i]->ts < Civl_mem[i]->ts || Civl_snapshot#0[i] == Civl_mem[i])
           && Civl_pSet == Set_Union_4166(Civl_old_pSet, sps)
           && Civl_done_first == Civl_old_done_first[tid := true]))
}

implementation read_f(perm: One_4378)
{
  var {:pool "K"} k: int;
  var {:pool "V"} v: Value;

  /*** structured program:
    assert 1 <= perm->val->mem_index && perm->val->mem_index <= n;
    assert done_first[perm->val->t_id] <==> false;
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

    call One_Put_3301(pSet, perm);
    if (Set_IsSubset(WholeTidPermission(perm->val->t_id), pSet))
    {
        done_first[perm->val->t_id] := true;
    }
  **** end structured program */

  anon0:
    assume Trigger_read_f_v(v);
    assume Trigger_read_f_k(k);
    assume {:add_to_pool "A", 0, n} true;
    goto anon5_Then, anon5_Else;

  anon5_Else:
    r1[perm->val->t_id][perm->val->mem_index] := mem[perm->val->mem_index];
    goto anon3;

  anon3:
    pSet := Set_Add_3301(pSet, perm->val);
    goto anon6_Then, anon6_Else;

  anon6_Else:
    assume {:partition} !Set_IsSubset_3308(WholeTidPermission(perm->val->t_id), pSet);
    return;

  anon6_Then:
    assume {:partition} Set_IsSubset_3308(WholeTidPermission(perm->val->t_id), pSet);
    done_first[perm->val->t_id] := true;
    return;

  anon5_Then:
    assume {:add_to_pool "K", mem[perm->val->mem_index]->ts, k} {:add_to_pool "V", mem[perm->val->mem_index]->value, v} true;
    assume k < mem[perm->val->mem_index]->ts;
    r1[perm->val->t_id][perm->val->mem_index] := StampedValue(k, v);
    goto anon3;
}



procedure {:inline 1} read_f(perm: One_4378);
  modifies r1, pSet, done_first;



function {:inline} Civl_InputOutputRelation_read_f(perm: One_4378) : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_r1: [Tid][int]StampedValue, 
      Civl_old_r2: [Tid][int]StampedValue, 
      Civl_old_pSet: Set_4166, 
      Civl_old_done_first: [Tid]bool, 
      Civl_old_done_second: [Tid]bool, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4166, 
      Civl_done_first: [Tid]bool, 
      Civl_done_second: [Tid]bool :: 
    (Civl_old_done_first[perm->val->t_id] <==> false)
       && 
      1 <= perm->val->mem_index
       && perm->val->mem_index <= n
       && (
        (exists {:pool "K"} Civl_k#0: int, {:pool "V"} Civl_v#0: Value :: 
          true
             && true
             && Civl_k#0 < Civl_mem[perm->val->mem_index]->ts
             && Set_IsSubset_3308(WholeTidPermission(perm->val->t_id), Civl_pSet)
             && Civl_r1
               == Civl_old_r1[perm->val->t_id := Civl_old_r1[perm->val->t_id][perm->val->mem_index := StampedValue(Civl_k#0, Civl_v#0)]]
             && Civl_pSet == Set_Add_3301(Civl_old_pSet, perm->val)
             && Civl_done_first == Civl_old_done_first[perm->val->t_id := true])
         || (exists {:pool "K"} Civl_k#0: int, {:pool "V"} Civl_v#0: Value :: 
          true
             && true
             && Civl_k#0 < Civl_mem[perm->val->mem_index]->ts
             && !Set_IsSubset_3308(WholeTidPermission(perm->val->t_id), Civl_pSet)
             && Civl_r1
               == Civl_old_r1[perm->val->t_id := Civl_old_r1[perm->val->t_id][perm->val->mem_index := StampedValue(Civl_k#0, Civl_v#0)]]
             && Civl_pSet == Set_Add_3301(Civl_old_pSet, perm->val)
             && Civl_done_first == Civl_old_done_first)
         || (
          true
           && Set_IsSubset_3308(WholeTidPermission(perm->val->t_id), Civl_pSet)
           && Civl_r1
             == Civl_old_r1[perm->val->t_id := Civl_old_r1[perm->val->t_id][perm->val->mem_index := Civl_mem[perm->val->mem_index]]]
           && Civl_pSet == Set_Add_3301(Civl_old_pSet, perm->val)
           && Civl_done_first == Civl_old_done_first[perm->val->t_id := true])
         || (
          true
           && !Set_IsSubset_3308(WholeTidPermission(perm->val->t_id), Civl_pSet)
           && Civl_r1
             == Civl_old_r1[perm->val->t_id := Civl_old_r1[perm->val->t_id][perm->val->mem_index := Civl_mem[perm->val->mem_index]]]
           && Civl_pSet == Set_Add_3301(Civl_old_pSet, perm->val)
           && Civl_done_first == Civl_old_done_first)))
}

implementation Inv_f(tid: Tid, sps: Set_4166) returns (Civl_PAs_read_f: [read_f]int)
{
  var {:pool "A"} j: int;
  var sps2: Set_4166;
  var done_set: Set_4166;
  var choice: read_f;

  /*** structured program:
    assert sps == WholeTidPermission(tid);
    assert done_first[tid] <==> false;
    assume {:add_to_pool "A", 0, j + 1, n} 0 <= j && j <= n;
    havoc r1;
    assume (forall i: int :: 
      1 <= i && i <= j ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i]);
    assume {:add_to_pool "D", Permission(tid, n)} true;
    sps2 := sps;
    call done_set := Set_Get_3352(sps2, (lambda {:pool "D"} x: Permission :: 
      x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j));
    call Set_Put_3301(pSet, done_set);
    if (j < n)
    {
        choice := read_f(One_4378(Permission(tid, j + 1)));
        assume {:add_to_pool "C", choice} true;
        call create_asyncs((lambda {:pool "C"} pa: read_f :: 
          j + 1 <= pa->perm->val->mem_index
             && pa->perm->val->mem_index <= n
             && pa->perm->val->t_id == tid));
        call set_choice(choice);
    }
    else
    {
        done_first[tid] := true;
    }
  **** end structured program */

  anon0:
    assume Trigger_Inv_f_j(j);
    Civl_PAs_read_f := MapConst_3_8314(0);
    assume {:add_to_pool "A", 0, j + 1, n} 0 <= j && j <= n;
    havoc r1;
    assume (forall i: int :: 
      1 <= i && i <= j ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i]);
    assume {:add_to_pool "D", Permission(tid, n)} true;
    sps2 := sps;
    done_set := Set_4166((lambda {:pool "D"} x: Permission :: 
        x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j));
    sps2 := Set_Difference_4166(sps2, done_set);
    pSet := Set_Union_4166(pSet, done_set);
    goto anon3_Then, anon3_Else;

  anon3_Else:
    assume {:partition} n <= j;
    done_first[tid] := true;
    return;

  anon3_Then:
    assume {:partition} j < n;
    choice := read_f(One_4378(Permission(tid, j + 1)));
    assume {:add_to_pool "C", choice} true;
    Civl_PAs_read_f := MapAdd_8303(Civl_PAs_read_f, 
      MapIte_8321_3((lambda {:pool "C"} pa: read_f :: 
          j + 1 <= pa->perm->val->mem_index
             && pa->perm->val->mem_index <= n
             && pa->perm->val->t_id == tid), 
        MapConst_3_8314(1), 
        MapConst_3_8314(0)));
    return;
}



procedure {:inline 1} Inv_f(tid: Tid, sps: Set_4166) returns (Civl_PAs_read_f: [read_f]int);
  modifies r1, pSet, done_first;



function {:inline} Civl_InputOutputRelation_Inv_f(tid: Tid, sps: Set_4166, Civl_PAs_read_f: [read_f]int) : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_r1: [Tid][int]StampedValue, 
      Civl_old_r2: [Tid][int]StampedValue, 
      Civl_old_pSet: Set_4166, 
      Civl_old_done_first: [Tid]bool, 
      Civl_old_done_second: [Tid]bool, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4166, 
      Civl_done_first: [Tid]bool, 
      Civl_done_second: [Tid]bool :: 
    (forall j: int :: 
        0 <= j && j <= n
           ==> (forall r1: [Tid][int]StampedValue :: 
            (forall i: int :: 
                1 <= i && i <= j
                   ==> r1[tid][i]->ts < Civl_old_mem[i]->ts || r1[tid][i] == Civl_old_mem[i])
               ==> 
              true
               ==> Set_IsSubset_3308(Set_4166((lambda {:pool "D"} x: Permission :: 
                    x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j)), 
                sps)))
       && (Civl_old_done_first[tid] <==> false)
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
             && Civl_pSet
               == Set_Union_4166(Civl_old_pSet, 
                Set_4166((lambda {:pool "D"} x: Permission :: 
                    x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
             && Civl_PAs_read_f
               == MapAdd_8303(MapConst_3_8314(0), 
                MapIte_8321_3((lambda {:pool "C"} pa: read_f :: 
                    Civl_j#0 + 1 <= pa->perm->val->mem_index
                       && pa->perm->val->mem_index <= n
                       && pa->perm->val->t_id == tid), 
                  MapConst_3_8314(1), 
                  MapConst_3_8314(0)))
             && Civl_done_first == Civl_old_done_first)
         || (exists {:pool "A"} Civl_j#0: int :: 
          0 <= Civl_j#0
             && Civl_j#0 <= n
             && (forall i: int :: 
              1 <= i && i <= Civl_j#0
                 ==> Civl_r1[tid][i]->ts < Civl_mem[i]->ts || Civl_r1[tid][i] == Civl_mem[i])
             && true
             && n <= Civl_j#0
             && Civl_PAs_read_f == MapConst_3_8314(0)
             && Civl_pSet
               == Set_Union_4166(Civl_old_pSet, 
                Set_4166((lambda {:pool "D"} x: Permission :: 
                    x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
             && Civl_done_first == Civl_old_done_first[tid := true])))
}

implementation Inv_f_With_Choice(tid: Tid, sps: Set_4166)
   returns (Civl_PAs_read_f: [read_f]int, Civl_choice: Choice_Inv_f)
{
  var {:pool "A"} j: int;
  var sps2: Set_4166;
  var done_set: Set_4166;
  var choice: read_f;

  /*** structured program:
    assert sps == WholeTidPermission(tid);
    assert done_first[tid] <==> false;
    assume {:add_to_pool "A", 0, j + 1, n} 0 <= j && j <= n;
    havoc r1;
    assume (forall i: int :: 
      1 <= i && i <= j ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i]);
    assume {:add_to_pool "D", Permission(tid, n)} true;
    sps2 := sps;
    call done_set := Set_Get_3352(sps2, (lambda {:pool "D"} x: Permission :: 
      x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j));
    call Set_Put_3301(pSet, done_set);
    if (j < n)
    {
        choice := read_f(One_4378(Permission(tid, j + 1)));
        assume {:add_to_pool "C", choice} true;
        call create_asyncs((lambda {:pool "C"} pa: read_f :: 
          j + 1 <= pa->perm->val->mem_index
             && pa->perm->val->mem_index <= n
             && pa->perm->val->t_id == tid));
        call set_choice(choice);
    }
    else
    {
        done_first[tid] := true;
    }
  **** end structured program */

  anon0:
    Civl_PAs_read_f := MapConst_3_8314(0);
    assert sps == WholeTidPermission(tid);
    assert done_first[tid] <==> false;
    assume {:add_to_pool "A", 0, j + 1, n} 0 <= j && j <= n;
    havoc r1;
    assume (forall i: int :: 
      1 <= i && i <= j ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i]);
    assume {:add_to_pool "D", Permission(tid, n)} true;
    sps2 := sps;
    done_set := Set_4166((lambda {:pool "D"} x: Permission :: 
        x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j));
    assert Set_IsSubset_3308(done_set, sps2);
    sps2 := Set_Difference_4166(sps2, done_set);
    pSet := Set_Union_4166(pSet, done_set);
    goto anon3_Then, anon3_Else;

  anon3_Else:
    assume {:partition} n <= j;
    done_first[tid] := true;
    return;

  anon3_Then:
    assume {:partition} j < n;
    choice := read_f(One_4378(Permission(tid, j + 1)));
    assume {:add_to_pool "C", choice} true;
    Civl_PAs_read_f := MapAdd_8303(Civl_PAs_read_f, 
      MapIte_8321_3((lambda {:pool "C"} pa: read_f :: 
          j + 1 <= pa->perm->val->mem_index
             && pa->perm->val->mem_index <= n
             && pa->perm->val->t_id == tid), 
        MapConst_3_8314(1), 
        MapConst_3_8314(0)));
    assert Civl_PAs_read_f == MapConst_3_8314(0) || Civl_PAs_read_f[choice] > 0;
    Civl_choice->read_f := choice;
    return;
}



procedure {:inline 1} Inv_f_With_Choice(tid: Tid, sps: Set_4166)
   returns (Civl_PAs_read_f: [read_f]int, Civl_choice: Choice_Inv_f);
  modifies r1, pSet, done_first;



function {:inline} Civl_InputOutputRelation_Inv_f_With_Choice(tid: Tid, sps: Set_4166, Civl_PAs_read_f: [read_f]int, Civl_choice: Choice_Inv_f)
   : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_r1: [Tid][int]StampedValue, 
      Civl_old_r2: [Tid][int]StampedValue, 
      Civl_old_pSet: Set_4166, 
      Civl_old_done_first: [Tid]bool, 
      Civl_old_done_second: [Tid]bool, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4166, 
      Civl_done_first: [Tid]bool, 
      Civl_done_second: [Tid]bool :: 
    (forall j: int :: 
        0 <= j && j <= n
           ==> (forall r1: [Tid][int]StampedValue :: 
            (forall i: int :: 
                1 <= i && i <= j
                   ==> r1[tid][i]->ts < Civl_old_mem[i]->ts || r1[tid][i] == Civl_old_mem[i])
               ==> 
              true
               ==> Set_IsSubset_3308(Set_4166((lambda {:pool "D"} x: Permission :: 
                    x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j)), 
                sps)))
       && (Civl_old_done_first[tid] <==> false)
       && sps == WholeTidPermission(tid)
       && ((exists {:pool "A"} Civl_j#0: int :: 
          sps == WholeTidPermission(tid)
             && (Civl_done_first[tid] <==> false)
             && 0 <= Civl_j#0
             && Civl_j#0 <= n
             && (forall i: int :: 
              1 <= i && i <= Civl_j#0
                 ==> Civl_r1[tid][i]->ts < Civl_mem[i]->ts || Civl_r1[tid][i] == Civl_mem[i])
             && true
             && Set_IsSubset_3308(Set_4166((lambda {:pool "D"} x: Permission :: 
                  x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)), 
              sps)
             && Civl_j#0 < n
             && true
             && (Civl_PAs_read_f == MapConst_3_8314(0)
               || Civl_PAs_read_f[read_f(One_4378(Permission(tid, Civl_j#0 + 1)))] > 0)
             && Civl_pSet
               == Set_Union_4166(Civl_old_pSet, 
                Set_4166((lambda {:pool "D"} x: Permission :: 
                    x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
             && Civl_PAs_read_f
               == MapAdd_8303(MapConst_3_8314(0), 
                MapIte_8321_3((lambda {:pool "C"} pa: read_f :: 
                    Civl_j#0 + 1 <= pa->perm->val->mem_index
                       && pa->perm->val->mem_index <= n
                       && pa->perm->val->t_id == tid), 
                  MapConst_3_8314(1), 
                  MapConst_3_8314(0)))
             && Civl_choice
               == Choice_Inv_f_read_f(read_f(One_4378(Permission(tid, Civl_j#0 + 1))))
             && Civl_done_first == Civl_old_done_first)
         || (exists {:pool "A"} Civl_j#0: int :: 
          sps == WholeTidPermission(tid)
             && (Civl_old_done_first[tid] <==> false)
             && 0 <= Civl_j#0
             && Civl_j#0 <= n
             && (forall i: int :: 
              1 <= i && i <= Civl_j#0
                 ==> Civl_r1[tid][i]->ts < Civl_mem[i]->ts || Civl_r1[tid][i] == Civl_mem[i])
             && true
             && Set_IsSubset_3308(Set_4166((lambda {:pool "D"} x: Permission :: 
                  x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)), 
              sps)
             && n <= Civl_j#0
             && Civl_PAs_read_f == MapConst_3_8314(0)
             && Civl_pSet
               == Set_Union_4166(Civl_old_pSet, 
                Set_4166((lambda {:pool "D"} x: Permission :: 
                    x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
             && Civl_done_first == Civl_old_done_first[tid := true])))
}

implementation action_main_f(tid: Tid, sps: Set_4166) returns (Civl_PAs_read_f: [read_f]int)
{
  /*** structured program:
    assume {:add_to_pool "A", 0, n} true;
    assert sps == WholeTidPermission(tid);
    assert done_first[tid] <==> false;
    call create_asyncs_3324((lambda pa: read_f :: 
      1 <= pa->perm->val->mem_index
         && pa->perm->val->mem_index <= n
         && pa->perm->val->t_id == tid));
  **** end structured program */

  anon0:
    Civl_PAs_read_f := MapConst_3_8314(0);
    assume {:add_to_pool "A", 0, n} true;
    Civl_PAs_read_f := MapAdd_8303(Civl_PAs_read_f, 
      MapIte_8321_3((lambda pa: read_f :: 
          1 <= pa->perm->val->mem_index
             && pa->perm->val->mem_index <= n
             && pa->perm->val->t_id == tid), 
        MapConst_3_8314(1), 
        MapConst_3_8314(0)));
    return;
}



procedure {:inline 1} action_main_f(tid: Tid, sps: Set_4166) returns (Civl_PAs_read_f: [read_f]int);



function {:inline} Civl_InputOutputRelation_action_main_f(tid: Tid, sps: Set_4166, Civl_PAs_read_f: [read_f]int) : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_r1: [Tid][int]StampedValue, 
      Civl_old_r2: [Tid][int]StampedValue, 
      Civl_old_pSet: Set_4166, 
      Civl_old_done_first: [Tid]bool, 
      Civl_old_done_second: [Tid]bool, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4166, 
      Civl_done_first: [Tid]bool, 
      Civl_done_second: [Tid]bool :: 
    (true ==> (Civl_old_done_first[tid] <==> false))
       && (true ==> sps == WholeTidPermission(tid))
       && 
      true
       && Civl_PAs_read_f
         == MapAdd_8303(MapConst_3_8314(0), 
          MapIte_8321_3((lambda pa: read_f :: 
              1 <= pa->perm->val->mem_index
                 && pa->perm->val->mem_index <= n
                 && pa->perm->val->t_id == tid), 
            MapConst_3_8314(1), 
            MapConst_3_8314(0))))
}

implementation Civl_CommutativityChecker_read_f_write_1(first_perm: One_4378, second_i: int, second_v: Value)
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
             && Set_IsSubset_3308(WholeTidPermission(first_perm->val->t_id), pSet)
             && mem == old(mem)[second_i := StampedValue(old(mem)[second_i]->ts + 1, second_v)]
             && r1
               == old(r1)[first_perm->val->t_id := old(r1)[first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3301(old(pSet), first_perm->val)
             && done_first == old(done_first)[first_perm->val->t_id := true])
         || (exists {:pool "K"} Civl_first_k#0: int, {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && !Set_IsSubset_3308(WholeTidPermission(first_perm->val->t_id), pSet)
             && mem == old(mem)[second_i := StampedValue(old(mem)[second_i]->ts + 1, second_v)]
             && r1
               == old(r1)[first_perm->val->t_id := old(r1)[first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3301(old(pSet), first_perm->val)
             && done_first == old(done_first))
         || (
          true
           && Set_IsSubset_3308(WholeTidPermission(first_perm->val->t_id), pSet)
           && mem == old(mem)[second_i := StampedValue(old(mem)[second_i]->ts + 1, second_v)]
           && r1
             == old(r1)[first_perm->val->t_id := old(r1)[first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet == Set_Add_3301(old(pSet), first_perm->val)
           && done_first == old(done_first)[first_perm->val->t_id := true])
         || (
          true
           && !Set_IsSubset_3308(WholeTidPermission(first_perm->val->t_id), pSet)
           && mem == old(mem)[second_i := StampedValue(old(mem)[second_i]->ts + 1, second_v)]
           && r1
             == old(r1)[first_perm->val->t_id := old(r1)[first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet == Set_Add_3301(old(pSet), first_perm->val)
           && done_first == old(done_first));
    return;
}



procedure Civl_CommutativityChecker_read_f_write_1(first_perm: One_4378, second_i: int, second_v: Value);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3308(One_Collector_4378(first_perm), 
          MapEq_4166_3(Civl_partition_Permission, MapConst_3_4166(0)))
         == MapConst_5_3308(true)
       && MapImp_3308(Set_Collector_4166(pSet), 
          MapEq_4166_3(Civl_partition_Permission, MapConst_3_4166(1)))
         == MapConst_5_3308(true));
  requires done_first[first_perm->val->t_id] <==> false;
  requires 1 <= first_perm->val->mem_index && first_perm->val->mem_index <= n;
  requires !Set_IsSubset_3308(WholeTidPermission(first_perm->val->t_id), Set_Add_3301(pSet, first_perm->val));
  modifies mem, r1, r2, pSet, done_first, done_second;



implementation Civl_CommutativityChecker_read_f_read_f_1(first_perm: One_4378, second_perm: One_4378)
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
             && Set_IsSubset_3308(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3301(old(pSet), second_perm->val))
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && Set_IsSubset_3308(WholeTidPermission(first_perm->val->t_id), pSet)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3301(Set_Add_3301(old(pSet), second_perm->val), first_perm->val)
             && done_first
               == old(done_first)[second_perm->val->t_id := true][first_perm->val->t_id := true]
             && mem == old(mem))
         || (exists {:pool "K"} Civl_second_k#0: int, 
            {:pool "K"} Civl_first_k#0: int, 
            {:pool "V"} Civl_second_v#0: Value, 
            {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_second_v#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && Set_IsSubset_3308(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3301(old(pSet), second_perm->val))
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && !Set_IsSubset_3308(WholeTidPermission(first_perm->val->t_id), pSet)
             && done_first == old(done_first)[second_perm->val->t_id := true]
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3301(Set_Add_3301(old(pSet), second_perm->val), first_perm->val)
             && mem == old(mem))
         || (exists {:pool "K"} Civl_second_k#0: int, {:pool "V"} Civl_second_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_v(Civl_second_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && Set_IsSubset_3308(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3301(old(pSet), second_perm->val))
             && true
             && Set_IsSubset_3308(WholeTidPermission(first_perm->val->t_id), pSet)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
             && pSet == Set_Add_3301(Set_Add_3301(old(pSet), second_perm->val), first_perm->val)
             && done_first
               == old(done_first)[second_perm->val->t_id := true][first_perm->val->t_id := true]
             && mem == old(mem))
         || (exists {:pool "K"} Civl_second_k#0: int, {:pool "V"} Civl_second_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_v(Civl_second_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && Set_IsSubset_3308(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3301(old(pSet), second_perm->val))
             && true
             && !Set_IsSubset_3308(WholeTidPermission(first_perm->val->t_id), pSet)
             && done_first == old(done_first)[second_perm->val->t_id := true]
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
             && pSet == Set_Add_3301(Set_Add_3301(old(pSet), second_perm->val), first_perm->val)
             && mem == old(mem))
         || (exists {:pool "K"} Civl_second_k#0: int, 
            {:pool "K"} Civl_first_k#0: int, 
            {:pool "V"} Civl_second_v#0: Value, 
            {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_second_v#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && !Set_IsSubset_3308(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3301(old(pSet), second_perm->val))
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && Set_IsSubset_3308(WholeTidPermission(first_perm->val->t_id), pSet)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3301(Set_Add_3301(old(pSet), second_perm->val), first_perm->val)
             && done_first == old(done_first)[first_perm->val->t_id := true]
             && mem == old(mem))
         || (exists {:pool "K"} Civl_second_k#0: int, 
            {:pool "K"} Civl_first_k#0: int, 
            {:pool "V"} Civl_second_v#0: Value, 
            {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_second_v#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && !Set_IsSubset_3308(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3301(old(pSet), second_perm->val))
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && !Set_IsSubset_3308(WholeTidPermission(first_perm->val->t_id), pSet)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3301(Set_Add_3301(old(pSet), second_perm->val), first_perm->val)
             && done_first == old(done_first)
             && mem == old(mem))
         || (exists {:pool "K"} Civl_second_k#0: int, {:pool "V"} Civl_second_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_v(Civl_second_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && !Set_IsSubset_3308(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3301(old(pSet), second_perm->val))
             && true
             && Set_IsSubset_3308(WholeTidPermission(first_perm->val->t_id), pSet)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
             && pSet == Set_Add_3301(Set_Add_3301(old(pSet), second_perm->val), first_perm->val)
             && done_first == old(done_first)[first_perm->val->t_id := true]
             && mem == old(mem))
         || (exists {:pool "K"} Civl_second_k#0: int, {:pool "V"} Civl_second_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_v(Civl_second_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && !Set_IsSubset_3308(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3301(old(pSet), second_perm->val))
             && true
             && !Set_IsSubset_3308(WholeTidPermission(first_perm->val->t_id), pSet)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
             && pSet == Set_Add_3301(Set_Add_3301(old(pSet), second_perm->val), first_perm->val)
             && done_first == old(done_first)
             && mem == old(mem))
         || (exists {:pool "K"} Civl_first_k#0: int, {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && Set_IsSubset_3308(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3301(old(pSet), second_perm->val))
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && Set_IsSubset_3308(WholeTidPermission(first_perm->val->t_id), pSet)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3301(Set_Add_3301(old(pSet), second_perm->val), first_perm->val)
             && done_first
               == old(done_first)[second_perm->val->t_id := true][first_perm->val->t_id := true]
             && mem == old(mem))
         || (exists {:pool "K"} Civl_first_k#0: int, {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && Set_IsSubset_3308(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3301(old(pSet), second_perm->val))
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && !Set_IsSubset_3308(WholeTidPermission(first_perm->val->t_id), pSet)
             && done_first == old(done_first)[second_perm->val->t_id := true]
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3301(Set_Add_3301(old(pSet), second_perm->val), first_perm->val)
             && mem == old(mem))
         || (
          true
           && Set_IsSubset_3308(WholeTidPermission(second_perm->val->t_id), 
            Set_Add_3301(old(pSet), second_perm->val))
           && true
           && Set_IsSubset_3308(WholeTidPermission(first_perm->val->t_id), pSet)
           && r1
             == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet == Set_Add_3301(Set_Add_3301(old(pSet), second_perm->val), first_perm->val)
           && done_first
             == old(done_first)[second_perm->val->t_id := true][first_perm->val->t_id := true]
           && mem == old(mem))
         || (
          true
           && Set_IsSubset_3308(WholeTidPermission(second_perm->val->t_id), 
            Set_Add_3301(old(pSet), second_perm->val))
           && true
           && !Set_IsSubset_3308(WholeTidPermission(first_perm->val->t_id), pSet)
           && done_first == old(done_first)[second_perm->val->t_id := true]
           && r1
             == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet == Set_Add_3301(Set_Add_3301(old(pSet), second_perm->val), first_perm->val)
           && mem == old(mem))
         || (exists {:pool "K"} Civl_first_k#0: int, {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && !Set_IsSubset_3308(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3301(old(pSet), second_perm->val))
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && Set_IsSubset_3308(WholeTidPermission(first_perm->val->t_id), pSet)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3301(Set_Add_3301(old(pSet), second_perm->val), first_perm->val)
             && done_first == old(done_first)[first_perm->val->t_id := true]
             && mem == old(mem))
         || (exists {:pool "K"} Civl_first_k#0: int, {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && !Set_IsSubset_3308(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3301(old(pSet), second_perm->val))
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && !Set_IsSubset_3308(WholeTidPermission(first_perm->val->t_id), pSet)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3301(Set_Add_3301(old(pSet), second_perm->val), first_perm->val)
             && done_first == old(done_first)
             && mem == old(mem))
         || (
          true
           && !Set_IsSubset_3308(WholeTidPermission(second_perm->val->t_id), 
            Set_Add_3301(old(pSet), second_perm->val))
           && true
           && Set_IsSubset_3308(WholeTidPermission(first_perm->val->t_id), pSet)
           && r1
             == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet == Set_Add_3301(Set_Add_3301(old(pSet), second_perm->val), first_perm->val)
           && done_first == old(done_first)[first_perm->val->t_id := true]
           && mem == old(mem))
         || (
          true
           && !Set_IsSubset_3308(WholeTidPermission(second_perm->val->t_id), 
            Set_Add_3301(old(pSet), second_perm->val))
           && true
           && !Set_IsSubset_3308(WholeTidPermission(first_perm->val->t_id), pSet)
           && r1
             == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet == Set_Add_3301(Set_Add_3301(old(pSet), second_perm->val), first_perm->val)
           && done_first == old(done_first)
           && mem == old(mem));
    return;
}



procedure Civl_CommutativityChecker_read_f_read_f_1(first_perm: One_4378, second_perm: One_4378);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3308(One_Collector_4378(first_perm), 
          MapEq_4166_3(Civl_partition_Permission, MapConst_3_4166(0)))
         == MapConst_5_3308(true)
       && MapImp_3308(One_Collector_4378(second_perm), 
          MapEq_4166_3(Civl_partition_Permission, MapConst_3_4166(1)))
         == MapConst_5_3308(true)
       && MapImp_3308(Set_Collector_4166(pSet), 
          MapEq_4166_3(Civl_partition_Permission, MapConst_3_4166(2)))
         == MapConst_5_3308(true));
  requires done_first[first_perm->val->t_id] <==> false;
  requires 1 <= first_perm->val->mem_index && first_perm->val->mem_index <= n;
  requires done_first[second_perm->val->t_id] <==> false;
  requires 1 <= second_perm->val->mem_index && second_perm->val->mem_index <= n;
  requires !Set_IsSubset_3308(WholeTidPermission(first_perm->val->t_id), Set_Add_3301(pSet, first_perm->val));
  modifies mem, r1, r2, pSet, done_first, done_second;



implementation Civl_GatePreservationChecker_read_f_read_f_1(first_perm: One_4378, second_perm: One_4378)
{

  init:
    call read_f(second_perm);
    assert (exists Civl_partition_Permission: [Permission]int :: 
        MapImp_3308(One_Collector_4378(first_perm), 
              MapEq_4166_3(Civl_partition_Permission, MapConst_3_4166(0)))
             == MapConst_5_3308(true)
           && MapImp_3308(Set_Collector_4166(pSet), 
              MapEq_4166_3(Civl_partition_Permission, MapConst_3_4166(1)))
             == MapConst_5_3308(true))
       ==> (done_first[first_perm->val->t_id] <==> false);
    assert (exists Civl_partition_Permission: [Permission]int :: 
        MapImp_3308(One_Collector_4378(first_perm), 
              MapEq_4166_3(Civl_partition_Permission, MapConst_3_4166(0)))
             == MapConst_5_3308(true)
           && MapImp_3308(Set_Collector_4166(pSet), 
              MapEq_4166_3(Civl_partition_Permission, MapConst_3_4166(1)))
             == MapConst_5_3308(true))
       ==> 1 <= first_perm->val->mem_index && first_perm->val->mem_index <= n;
    return;
}



procedure Civl_GatePreservationChecker_read_f_read_f_1(first_perm: One_4378, second_perm: One_4378);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3308(One_Collector_4378(first_perm), 
          MapEq_4166_3(Civl_partition_Permission, MapConst_3_4166(0)))
         == MapConst_5_3308(true)
       && MapImp_3308(One_Collector_4378(second_perm), 
          MapEq_4166_3(Civl_partition_Permission, MapConst_3_4166(1)))
         == MapConst_5_3308(true)
       && MapImp_3308(Set_Collector_4166(pSet), 
          MapEq_4166_3(Civl_partition_Permission, MapConst_3_4166(2)))
         == MapConst_5_3308(true));
  requires done_first[first_perm->val->t_id] <==> false;
  requires 1 <= first_perm->val->mem_index && first_perm->val->mem_index <= n;
  requires done_first[second_perm->val->t_id] <==> false;
  requires 1 <= second_perm->val->mem_index && second_perm->val->mem_index <= n;
  requires !Set_IsSubset_3308(WholeTidPermission(second_perm->val->t_id), Set_Add_3301(pSet, second_perm->val));
  modifies mem, r1, r2, pSet, done_first, done_second;



implementation Civl_GatePreservationChecker_action_main_f_read_f_1(first_tid: Tid, first_sps: Set_4166, second_perm: One_4378)
   returns (first_Civl_PAs_read_f: [read_f]int)
{

  init:
    call read_f(second_perm);
    assert (exists Civl_partition_Permission: [Permission]int :: 
        MapImp_3308(Set_Collector_4166(first_sps), 
              MapEq_4166_3(Civl_partition_Permission, MapConst_3_4166(0)))
             == MapConst_5_3308(true)
           && MapImp_3308(Set_Collector_4166(pSet), 
              MapEq_4166_3(Civl_partition_Permission, MapConst_3_4166(1)))
             == MapConst_5_3308(true))
       ==> 
      true
       ==> (done_first[first_tid] <==> false);
    assert (exists Civl_partition_Permission: [Permission]int :: 
        MapImp_3308(Set_Collector_4166(first_sps), 
              MapEq_4166_3(Civl_partition_Permission, MapConst_3_4166(0)))
             == MapConst_5_3308(true)
           && MapImp_3308(Set_Collector_4166(pSet), 
              MapEq_4166_3(Civl_partition_Permission, MapConst_3_4166(1)))
             == MapConst_5_3308(true))
       ==> 
      true
       ==> first_sps == WholeTidPermission(first_tid);
    return;
}



procedure Civl_GatePreservationChecker_action_main_f_read_f_1(first_tid: Tid, first_sps: Set_4166, second_perm: One_4378)
   returns (first_Civl_PAs_read_f: [read_f]int);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3308(Set_Collector_4166(first_sps), 
          MapEq_4166_3(Civl_partition_Permission, MapConst_3_4166(0)))
         == MapConst_5_3308(true)
       && MapImp_3308(One_Collector_4378(second_perm), 
          MapEq_4166_3(Civl_partition_Permission, MapConst_3_4166(1)))
         == MapConst_5_3308(true)
       && MapImp_3308(Set_Collector_4166(pSet), 
          MapEq_4166_3(Civl_partition_Permission, MapConst_3_4166(2)))
         == MapConst_5_3308(true));
  requires true ==> (done_first[first_tid] <==> false);
  requires true ==> first_sps == WholeTidPermission(first_tid);
  requires done_first[second_perm->val->t_id] <==> false;
  requires 1 <= second_perm->val->mem_index && second_perm->val->mem_index <= n;
  requires !Set_IsSubset_3308(WholeTidPermission(second_perm->val->t_id), Set_Add_3301(pSet, second_perm->val));
  modifies mem, r1, r2, pSet, done_first, done_second;



procedure Civl_PendingAsyncNoninterferenceChecker_read_f_1(perm: One_4378);
  requires done_first[perm->val->t_id] <==> false;
  requires 1 <= perm->val->mem_index && perm->val->mem_index <= n;
  modifies mem, r1, r2, pSet, done_first, done_second;



implementation Civl_PendingAsyncNoninterferenceChecker_read_f_1(perm: One_4378)
{
  var Civl_global_old_mem: [int]StampedValue;
  var Civl_global_old_r1: [Tid][int]StampedValue;
  var Civl_global_old_r2: [Tid][int]StampedValue;
  var Civl_global_old_pSet: Set_4166;
  var Civl_global_old_done_first: [Tid]bool;
  var Civl_global_old_done_second: [Tid]bool;
  var Civl_linear_Permission_available: [Permission]bool;

  init:
    Civl_global_old_mem, Civl_global_old_r1, Civl_global_old_r2, Civl_global_old_pSet, Civl_global_old_done_first, Civl_global_old_done_second := mem, r1, r2, pSet, done_first, done_second;
    Civl_linear_Permission_available := MapOr_4166(Set_Collector_4166(pSet), 
      MapOr_4166(One_Collector_4378(perm), MapConst_5_3308(false)));
    call read_f(perm);
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Permission_available, Civl_global_old_mem, Civl_global_old_r1, Civl_global_old_r2, Civl_global_old_pSet, Civl_global_old_done_first, Civl_global_old_done_second);
    return;
}



procedure Civl_PendingAsyncNoninterferenceChecker_action_main_f_1(tid: Tid, sps: Set_4166) returns (Civl_PAs_read_f: [read_f]int);
  requires true ==> (done_first[tid] <==> false);
  requires true ==> sps == WholeTidPermission(tid);
  modifies mem, r1, r2, pSet, done_first, done_second;



implementation Civl_PendingAsyncNoninterferenceChecker_action_main_f_1(tid: Tid, sps: Set_4166) returns (Civl_PAs_read_f: [read_f]int)
{
  var Civl_global_old_mem: [int]StampedValue;
  var Civl_global_old_r1: [Tid][int]StampedValue;
  var Civl_global_old_r2: [Tid][int]StampedValue;
  var Civl_global_old_pSet: Set_4166;
  var Civl_global_old_done_first: [Tid]bool;
  var Civl_global_old_done_second: [Tid]bool;
  var Civl_linear_Permission_available: [Permission]bool;

  init:
    Civl_global_old_mem, Civl_global_old_r1, Civl_global_old_r2, Civl_global_old_pSet, Civl_global_old_done_first, Civl_global_old_done_second := mem, r1, r2, pSet, done_first, done_second;
    Civl_linear_Permission_available := MapOr_4166(Set_Collector_4166(pSet), 
      MapOr_4166(Set_Collector_4166(sps), MapConst_5_3308(false)));
    call Civl_PAs_read_f := action_main_f(tid, sps);
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Permission_available, Civl_global_old_mem, Civl_global_old_r1, Civl_global_old_r2, Civl_global_old_pSet, Civl_global_old_done_first, Civl_global_old_done_second);
    return;
}



procedure {:inline 1} Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Permission_in: [Permission]bool, 
    Civl_global_old_mem: [int]StampedValue, 
    Civl_global_old_r1: [Tid][int]StampedValue, 
    Civl_global_old_r2: [Tid][int]StampedValue, 
    Civl_global_old_pSet: Set_4166, 
    Civl_global_old_done_first: [Tid]bool, 
    Civl_global_old_done_second: [Tid]bool);



implementation Civl_Wrapper_NoninterferenceChecker_1(Civl_Civl_linear_Permission_in: [Permission]bool, 
    Civl_Civl_global_old_mem: [int]StampedValue, 
    Civl_Civl_global_old_r1: [Tid][int]StampedValue, 
    Civl_Civl_global_old_r2: [Tid][int]StampedValue, 
    Civl_Civl_global_old_pSet: Set_4166, 
    Civl_Civl_global_old_done_first: [Tid]bool, 
    Civl_Civl_global_old_done_second: [Tid]bool)
{

  enter:
    return;
}



implementation Civl_LinearityChecker_action_main_f(tid: Tid, sps: Set_4166) returns (Civl_PAs_read_f: [read_f]int)
{
  var Civl_pa1_read_f: read_f;
  var Civl_pa2_read_f: read_f;

  init:
    call Civl_PAs_read_f := action_main_f(tid, sps);
    goto Permission_out_of_thin_air_read_f, Permission_duplication_read_f, Permission_duplication_read_f_read_f;

  Permission_out_of_thin_air_read_f:
    assume Civl_pa1_read_f is read_f && Civl_PAs_read_f[Civl_pa1_read_f] >= 1;
    assert MapImp_3308(MapOr_4166(One_Collector_4378(Civl_pa1_read_f->perm), MapConst_5_3308(false)), 
        old(MapOr_4166(Set_Collector_4166(sps), MapConst_5_3308(false))))
       == MapConst_5_3308(true);
    return;

  Permission_duplication_read_f:
    assume Civl_pa1_read_f is read_f && Civl_PAs_read_f[Civl_pa1_read_f] >= 1;
    assert MapAnd_4166(MapConst_5_3308(false), 
        MapOr_4166(One_Collector_4378(Civl_pa1_read_f->perm), MapConst_5_3308(false)))
       == MapConst_5_3308(false);
    return;

  Permission_duplication_read_f_read_f:
    assume Civl_pa1_read_f != Civl_pa2_read_f
       && 
      Civl_pa1_read_f is read_f
       && Civl_pa2_read_f is read_f
       && 
      Civl_PAs_read_f[Civl_pa1_read_f] >= 1
       && Civl_PAs_read_f[Civl_pa2_read_f] >= 1;
    assert MapAnd_4166(MapOr_4166(One_Collector_4378(Civl_pa1_read_f->perm), MapConst_5_3308(false)), 
        MapOr_4166(One_Collector_4378(Civl_pa2_read_f->perm), MapConst_5_3308(false)))
       == MapConst_5_3308(false);
    return;
}



procedure Civl_LinearityChecker_action_main_f(tid: Tid, sps: Set_4166) returns (Civl_PAs_read_f: [read_f]int);
  requires true ==> (done_first[tid] <==> false);
  requires true ==> sps == WholeTidPermission(tid);
  requires true;



procedure Civl_PartitionChecker_action_main_f(tid: Tid, sps: Set_4166) returns (Civl_PAs_read_f: [read_f]int);
  requires true ==> (done_first[tid] <==> false);
  requires true ==> sps == WholeTidPermission(tid);
  requires true;



implementation Civl_PartitionChecker_action_main_f(tid: Tid, sps: Set_4166) returns (Civl_PAs_read_f: [read_f]int)
{
  var Civl_local_Civl_PAs_read_f: read_f;

  Civl_PartitionChecker_action_main_f:
    call Civl_PAs_read_f := action_main_f(tid, sps);
    assert Civl_PAs_read_f != MapConst_3_8314(0) ==> true;
    goto label_Civl_PAs_read_f;

  label_Civl_PAs_read_f:
    assume Civl_PAs_read_f[Civl_local_Civl_PAs_read_f] >= 1;
    assert done_first[Civl_local_Civl_PAs_read_f->perm->val->t_id] <==> false;
    assert 1 <= Civl_local_Civl_PAs_read_f->perm->val->mem_index
       && Civl_local_Civl_PAs_read_f->perm->val->mem_index <= n;
    return;
}



procedure Civl_PartitionChecker_read_f(perm: One_4378);
  requires done_first[perm->val->t_id] <==> false;
  requires 1 <= perm->val->mem_index && perm->val->mem_index <= n;
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3308(One_Collector_4378(perm), 
          MapEq_4166_3(Civl_partition_Permission, MapConst_3_4166(0)))
         == MapConst_5_3308(true)
       && MapImp_3308(Set_Collector_4166(pSet), 
          MapEq_4166_3(Civl_partition_Permission, MapConst_3_4166(1)))
         == MapConst_5_3308(true));
  modifies r1, pSet, done_first;



implementation Civl_PartitionChecker_read_f(perm: One_4378)
{

  Civl_PartitionChecker_read_f:
    call read_f(perm);
    assert false ==> true;
    return;
}



procedure Civl_ISR_base_action_main_f(tid: Tid, sps: Set_4166) returns (Civl_PAs_read_f: [read_f]int);
  requires (forall j: int :: 
    0 <= j && j <= n
       ==> (forall r1: [Tid][int]StampedValue :: 
        (forall i: int :: 
            1 <= i && i <= j ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i])
           ==> 
          true
           ==> Set_IsSubset_3308(Set_4166((lambda {:pool "D"} x: Permission :: 
                x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j)), 
            sps)));
  requires done_first[tid] <==> false;
  requires sps == WholeTidPermission(tid);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3308(Set_Collector_4166(sps), 
          MapEq_4166_3(Civl_partition_Permission, MapConst_3_4166(0)))
         == MapConst_5_3308(true)
       && MapImp_3308(Set_Collector_4166(pSet), 
          MapEq_4166_3(Civl_partition_Permission, MapConst_3_4166(1)))
         == MapConst_5_3308(true));
  modifies r1, pSet, done_first;



implementation Civl_ISR_base_action_main_f(tid: Tid, sps: Set_4166) returns (Civl_PAs_read_f: [read_f]int)
{

  ISR_base_action_main_f:
    assert true ==> (done_first[tid] <==> false);
    assert true ==> sps == WholeTidPermission(tid);
    call Civl_PAs_read_f := action_main_f(tid, sps);
    assert (exists {:pool "A"} Civl_j#0: int :: 
        0 <= Civl_j#0
           && Civl_j#0 <= n
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0 ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i])
           && true
           && Civl_j#0 < n
           && true
           && pSet
             == Set_Union_4166(old(pSet), 
              Set_4166((lambda {:pool "D"} x: Permission :: 
                  x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
           && Civl_PAs_read_f
             == MapAdd_8303(MapConst_3_8314(0), 
              MapIte_8321_3((lambda {:pool "C"} pa: read_f :: 
                  Civl_j#0 + 1 <= pa->perm->val->mem_index
                     && pa->perm->val->mem_index <= n
                     && pa->perm->val->t_id == tid), 
                MapConst_3_8314(1), 
                MapConst_3_8314(0)))
           && done_first == old(done_first))
       || (exists {:pool "A"} Civl_j#0: int :: 
        0 <= Civl_j#0
           && Civl_j#0 <= n
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0 ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i])
           && true
           && n <= Civl_j#0
           && Civl_PAs_read_f == MapConst_3_8314(0)
           && pSet
             == Set_Union_4166(old(pSet), 
              Set_4166((lambda {:pool "D"} x: Permission :: 
                  x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
           && done_first == old(done_first)[tid := true]);
    return;
}



procedure Civl_ISR_conclusion_action_main_f(tid: Tid, sps: Set_4166) returns (Civl_PAs_read_f: [read_f]int);
  requires true ==> (done_first[tid] <==> false);
  requires true ==> sps == WholeTidPermission(tid);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3308(Set_Collector_4166(sps), 
          MapEq_4166_3(Civl_partition_Permission, MapConst_3_4166(0)))
         == MapConst_5_3308(true)
       && MapImp_3308(Set_Collector_4166(pSet), 
          MapEq_4166_3(Civl_partition_Permission, MapConst_3_4166(1)))
         == MapConst_5_3308(true));
  modifies r1, pSet, done_first;



implementation Civl_ISR_conclusion_action_main_f(tid: Tid, sps: Set_4166) returns (Civl_PAs_read_f: [read_f]int)
{

  ISR_conclusion_action_main_f:
    assert (forall j: int :: 
      0 <= j && j <= n
         ==> (forall r1: [Tid][int]StampedValue :: 
          (forall i: int :: 
              1 <= i && i <= j ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i])
             ==> 
            true
             ==> Set_IsSubset_3308(Set_4166((lambda {:pool "D"} x: Permission :: 
                  x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j)), 
              sps)));
    assert done_first[tid] <==> false;
    assert sps == WholeTidPermission(tid);
    call Civl_PAs_read_f := Inv_f(tid, sps);
    assume Civl_PAs_read_f == MapConst_3_8314(0);
    assert (exists Civl_snapshot#0: [int]StampedValue :: 
      true
         && (forall i: int :: 
          1 <= i && i <= n
             ==> Civl_snapshot#0[i]->ts < mem[i]->ts || Civl_snapshot#0[i] == mem[i])
         && pSet == Set_Union_4166(old(pSet), sps)
         && done_first == old(done_first)[tid := true]
         && mem == old(mem)
         && r1 == old(r1)
         && r2 == old(r2)
         && done_second == old(done_second));
    return;
}



procedure Civl_ISR_step_Inv_f_read_f(tid: Tid, sps: Set_4166)
   returns (Civl_PAs_read_f: [read_f]int, Civl_choice: Choice_Inv_f);
  requires (forall j: int :: 
    0 <= j && j <= n
       ==> (forall r1: [Tid][int]StampedValue :: 
        (forall i: int :: 
            1 <= i && i <= j ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i])
           ==> 
          true
           ==> Set_IsSubset_3308(Set_4166((lambda {:pool "D"} x: Permission :: 
                x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j)), 
            sps)));
  requires done_first[tid] <==> false;
  requires sps == WholeTidPermission(tid);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3308(Set_Collector_4166(sps), 
          MapEq_4166_3(Civl_partition_Permission, MapConst_3_4166(0)))
         == MapConst_5_3308(true)
       && MapImp_3308(Set_Collector_4166(pSet), 
          MapEq_4166_3(Civl_partition_Permission, MapConst_3_4166(1)))
         == MapConst_5_3308(true));
  modifies r1, pSet, done_first;



implementation Civl_ISR_step_Inv_f_read_f(tid: Tid, sps: Set_4166)
   returns (Civl_PAs_read_f: [read_f]int, Civl_choice: Choice_Inv_f)
{

  ISR_step_Inv_f_read_f:
    call Civl_PAs_read_f, Civl_choice := Inv_f_With_Choice(tid, sps);
    assume Civl_choice is Choice_Inv_f_read_f;
    assume Civl_PAs_read_f[Civl_choice->read_f] > 0;
    Civl_PAs_read_f[Civl_choice->read_f] := Civl_PAs_read_f[Civl_choice->read_f] - 1;
    assert done_first[Civl_choice->read_f->perm->val->t_id] <==> false;
    assert 1 <= Civl_choice->read_f->perm->val->mem_index
       && Civl_choice->read_f->perm->val->mem_index <= n;
    call read_f(Civl_choice->read_f->perm);
    assert (exists {:pool "A"} Civl_j#0: int :: 
        0 <= Civl_j#0
           && Civl_j#0 <= n
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0 ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i])
           && true
           && Civl_j#0 < n
           && true
           && pSet
             == Set_Union_4166(old(pSet), 
              Set_4166((lambda {:pool "D"} x: Permission :: 
                  x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
           && Civl_PAs_read_f
             == MapAdd_8303(MapConst_3_8314(0), 
              MapIte_8321_3((lambda {:pool "C"} pa: read_f :: 
                  Civl_j#0 + 1 <= pa->perm->val->mem_index
                     && pa->perm->val->mem_index <= n
                     && pa->perm->val->t_id == tid), 
                MapConst_3_8314(1), 
                MapConst_3_8314(0)))
           && done_first == old(done_first))
       || (exists {:pool "A"} Civl_j#0: int :: 
        0 <= Civl_j#0
           && Civl_j#0 <= n
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0 ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i])
           && true
           && n <= Civl_j#0
           && Civl_PAs_read_f == MapConst_3_8314(0)
           && pSet
             == Set_Union_4166(old(pSet), 
              Set_4166((lambda {:pool "D"} x: Permission :: 
                  x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
           && done_first == old(done_first)[tid := true]);
    return;
}



procedure Civl_ISR_SideCondition_action_main_f(tid: Tid, sps: Set_4166) returns (Civl_PAs_read_f: [read_f]int);
  requires true ==> (done_first[tid] <==> false);
  requires true ==> sps == WholeTidPermission(tid);
  requires true;



implementation Civl_ISR_SideCondition_action_main_f(tid: Tid, sps: Set_4166) returns (Civl_PAs_read_f: [read_f]int)
{

  init:
    call Civl_PAs_read_f := action_main_f(tid, sps);
    goto Permission_only_put_perm_action_main_f;

  Permission_only_put_perm_action_main_f:
    assume true;
    assert MapImp_3308(old(MapConst_5_3308(false)), MapConst_5_3308(false))
       == MapConst_5_3308(true);
    return;
}



procedure Civl_ISR_AllPendingAsyncsInElim_read_f(perm: One_4378);
  modifies r1, pSet, done_first;



implementation Civl_ISR_AllPendingAsyncsInElim_read_f(perm: One_4378)
{

  ISR_AllPendingAsyncsInElim_read_f:
    assume !Set_IsSubset_3308(WholeTidPermission(perm->val->t_id), Set_Add_3301(pSet, perm->val));
    call read_f(perm);
    assert true;
    return;
}



procedure Civl_ISR_AllPendingAsyncsNotInElim_read_f(perm: One_4378);
  modifies r1, pSet, done_first;



implementation Civl_ISR_AllPendingAsyncsNotInElim_read_f(perm: One_4378)
{

  ISR_AllPendingAsyncsNotInElim_read_f:
    assume Set_IsSubset_3308(WholeTidPermission(perm->val->t_id), Set_Add_3301(pSet, perm->val));
    call read_f(perm);
    assert true;
    return;
}



procedure Civl_ISR_SideCondition_read_f(perm: One_4378);
  requires done_first[perm->val->t_id] <==> false;
  requires 1 <= perm->val->mem_index && perm->val->mem_index <= n;
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3308(One_Collector_4378(perm), 
          MapEq_4166_3(Civl_partition_Permission, MapConst_3_4166(0)))
         == MapConst_5_3308(true)
       && MapImp_3308(Set_Collector_4166(pSet), 
          MapEq_4166_3(Civl_partition_Permission, MapConst_3_4166(1)))
         == MapConst_5_3308(true));
  modifies r1, pSet, done_first;



implementation Civl_ISR_SideCondition_read_f(perm: One_4378)
{

  init:
    call read_f(perm);
    goto Permission_only_put_perm_read_f;

  Permission_only_put_perm_read_f:
    assume true;
    assert MapImp_3308(old(MapOr_4166(Set_Collector_4166(pSet), MapConst_5_3308(false))), 
        MapOr_4166(Set_Collector_4166(pSet), MapConst_5_3308(false)))
       == MapConst_5_3308(true);
    return;
}



procedure Civl_ISR_InconsistencyChecker_action_main_f_read_f_read_f();
  modifies r1, pSet, done_first;



implementation Civl_ISR_InconsistencyChecker_action_main_f_read_f_read_f()
{
  var Civl_E1_read_f: read_f;
  var Civl_E2_read_f: read_f;
  var Civl_tempg_mem: [int]StampedValue;
  var Civl_tempg_r1: [Tid][int]StampedValue;
  var Civl_tempg_r2: [Tid][int]StampedValue;
  var Civl_tempg_pSet: Set_4166;
  var Civl_tempg_done_first: [Tid]bool;
  var Civl_tempg_done_second: [Tid]bool;
  var Civl_templ_tid: Tid;
  var Civl_templ_sps: Set_4166;

  ISR_InconsistencyChecker_action_main_f_read_f_read_f:
    assume (true ==> (Civl_tempg_done_first[Civl_templ_tid] <==> false))
       && (true ==> Civl_templ_sps == WholeTidPermission(Civl_templ_tid))
       && true;
    assume MapAnd_4166(MapOr_4166(Set_Collector_4166(pSet), MapConst_5_3308(false)), 
          MapOr_4166(One_Collector_4378(Civl_E1_read_f->perm), MapConst_5_3308(false)))
         == MapConst_5_3308(false)
       && MapAnd_4166(MapOr_4166(Set_Collector_4166(pSet), MapConst_5_3308(false)), 
          MapOr_4166(One_Collector_4378(Civl_E2_read_f->perm), MapConst_5_3308(false)))
         == MapConst_5_3308(false)
       && MapAnd_4166(MapOr_4166(One_Collector_4378(Civl_E1_read_f->perm), MapConst_5_3308(false)), 
          MapOr_4166(One_Collector_4378(Civl_E2_read_f->perm), MapConst_5_3308(false)))
         == MapConst_5_3308(false);
    assume MapImp_3308(MapOr_4166(One_Collector_4378(Civl_E1_read_f->perm), MapConst_5_3308(false)), 
          MapOr_4166(Set_Collector_4166(Civl_templ_sps), MapConst_5_3308(false)))
         == MapConst_5_3308(true)
       && MapImp_3308(MapOr_4166(One_Collector_4378(Civl_E2_read_f->perm), MapConst_5_3308(false)), 
          MapOr_4166(Set_Collector_4166(Civl_templ_sps), MapConst_5_3308(false)))
         == MapConst_5_3308(true);
    assert !(
      (done_first[Civl_E1_read_f->perm->val->t_id] <==> false)
       && 
      1 <= Civl_E1_read_f->perm->val->mem_index
       && Civl_E1_read_f->perm->val->mem_index <= n
       && 
      Set_IsSubset_3308(WholeTidPermission(Civl_E2_read_f->perm->val->t_id), 
        Set_Add_3301(pSet, Civl_E2_read_f->perm->val))
       && 
      (done_first[Civl_E2_read_f->perm->val->t_id] <==> false)
       && 
      1 <= Civl_E2_read_f->perm->val->mem_index
       && Civl_E2_read_f->perm->val->mem_index <= n);
    return;
}


