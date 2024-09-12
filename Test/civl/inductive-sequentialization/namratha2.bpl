// Boogie program verifier version 3.1.6.0, Copyright (c) 2003-2014, Microsoft.
// Command Line Options: snapshot-scatter-gather.bpl /civlDesugaredFile:namratha2.bpl

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

var pSet: Set_4497;

var done_first: bool;

var done_second: bool;

function {:inline} WholeTidPermission(tid: Tid) : Set_4497
{
  Set_4497((lambda {:pool "D"} x: Permission :: 
      x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n))
}

datatype atomic_main_f {
  atomic_main_f(tid: Tid, sps: Set_4497)
}

datatype read_f {
  read_f(perm: One_4830)
}

datatype atomic_main_s {
  atomic_main_s(tid: Tid, sps: Set_4497)
}

const Identity: [int]int;

function {:inline} AtLeast(x: int) : [int]bool
{
  MapLe_1488(MapConst_1505_1488(x), Identity)
}

function {:inline} Range(from: int, n: int) : [int]bool
{
  MapDiff_1508(AtLeast(from), AtLeast(from + n))
}

type {:builtin "Seq"} Seq _;

pure procedure Assume(b: bool);
  ensures b;



datatype Set_4497 {
  Set_4497(val: [Permission]bool)
}

pure procedure Set_Get_3567(path: Set_4497, k: [Permission]bool) returns (l: Set_4497);



datatype One_4830 {
  One_4830(val: Permission)
}

procedure create_asyncs_3602(PAs: [read_f]bool);



pure procedure Set_Put_3567(path: Set_4497, l: Set_4497);



function {:inline} Set_Add_3567(a: Set_4497, t: Permission) : Set_4497
{
  Set_4497(a->val[t := true])
}

function {:inline} Set_IsSubset_3570(a: Set_4497, b: Set_4497) : bool
{
  IsSubset_3570(a->val, b->val)
}

function {:inline} IsSubset_3570(a: [Permission]bool, b: [Permission]bool) : bool
{
  MapImp_3570(a, b) == MapConst_5_3570(true)
}

function {:builtin "MapImp"} MapImp_3570([Permission]bool, [Permission]bool) : [Permission]bool;

function {:builtin "MapConst"} MapConst_5_3570(bool) : [Permission]bool;

pure procedure One_Put_3567(path: Set_4497, l: One_4830);



procedure set_choice_3648(choice: read_f);



function {:builtin "MapConst"} MapConst_1505_1488(int) : [int]int;

function {:builtin "MapLe"} MapLe_1488([int]int, [int]int) : [int]bool;

function {:inline} MapDiff_1508(a: [int]bool, b: [int]bool) : [int]bool
{
  MapAnd_1508(a, MapNot_1508(b))
}

function {:builtin "MapNot"} MapNot_1508([int]bool) : [int]bool;

function {:builtin "MapAnd"} MapAnd_1508([int]bool, [int]bool) : [int]bool;

datatype Vec_5 {
  Vec_5(contents: [int]bool, len: int)
}

function Default_5() : bool;

function {:builtin "MapConst"} MapConst_5_1529(bool) : [int]bool;

function {:builtin "MapIte"} MapIte_1529_5([int]bool, [int]bool, [int]bool) : [int]bool;

datatype Vec_1505 {
  Vec_1505(contents: [int]int, len: int)
}

function Default_1505() : int;

function {:builtin "MapIte"} MapIte_1529_1505([int]bool, [int]int, [int]int) : [int]int;

function {:inline} Set_Empty_4497() : Set_4497
{
  Set_4497(MapConst_5_3570(false))
}

function Set_Size_4497(a: Set_4497) : int;

function {:inline} Set_Contains_4497(a: Set_4497, t: Permission) : bool
{
  a->val[t]
}

function {:inline} Set_Remove_4497(a: Set_4497, t: Permission) : Set_4497
{
  Set_4497(a->val[t := false])
}

function {:inline} Set_Difference_4497(a: Set_4497, b: Set_4497) : Set_4497
{
  Set_4497(MapDiff_4497(a->val, b->val))
}

function {:inline} MapDiff_4497(a: [Permission]bool, b: [Permission]bool) : [Permission]bool
{
  MapAnd_4497(a, MapNot_4497(b))
}

function {:builtin "MapNot"} MapNot_4497([Permission]bool) : [Permission]bool;

function {:builtin "MapAnd"} MapAnd_4497([Permission]bool, [Permission]bool) : [Permission]bool;

function {:inline} Set_Intersection_4497(a: Set_4497, b: Set_4497) : Set_4497
{
  Set_4497(MapAnd_4497(a->val, b->val))
}

function {:inline} Set_Union_4497(a: Set_4497, b: Set_4497) : Set_4497
{
  Set_4497(MapOr_4497(a->val, b->val))
}

function {:builtin "MapOr"} MapOr_4497([Permission]bool, [Permission]bool) : [Permission]bool;

function Choice_3570(a: [Permission]bool) : Permission;

function Choice_1488(a: [int]bool) : int;

axiom n >= 1;

axiom (forall x: int :: Identity[x] == x);

axiom (forall x: Vec_1505 :: 
  { x->len } { x->contents } 
  MapIte_1529_1505(Range(0, x->len), MapConst_1505_1488(Default_1505()), x->contents)
     == MapConst_1505_1488(Default_1505()));

axiom (forall x: Vec_5 :: 
  { x->len } { x->contents } 
  MapIte_1529_5(Range(0, x->len), MapConst_5_1529(Default_5()), x->contents)
     == MapConst_5_1529(Default_5()));

axiom (forall x: Vec_1505 :: { x->len } x->len >= 0);

axiom (forall x: Vec_5 :: { x->len } x->len >= 0);

axiom (forall a: Set_4497 :: a == Set_Empty_4497() || 0 < Set_Size_4497(a));

axiom Set_Size_4497(Set_Empty_4497()) == 0;

axiom (forall a: Set_4497, t: Permission :: 
  { Set_Add_3567(a, t) } 
  Set_Size_4497(Set_Add_3567(a, t))
     == (if Set_Contains_4497(a, t) then Set_Size_4497(a) else Set_Size_4497(a) + 1));

axiom (forall a: Set_4497, t: Permission :: 
  { Set_Remove_4497(a, t) } 
  Set_Size_4497(Set_Remove_4497(a, t))
     == (if Set_Contains_4497(a, t) then Set_Size_4497(a) - 1 else Set_Size_4497(a)));

axiom (forall a: Set_4497, b: Set_4497 :: 
  { Set_Difference_4497(a, b) } 
    { Set_Intersection_4497(a, b) } 
    { Set_Union_4497(a, b) } 
  Set_Size_4497(a)
     == Set_Size_4497(Set_Difference_4497(a, b))
       + Set_Size_4497(Set_Intersection_4497(a, b)));

axiom (forall a: Set_4497, b: Set_4497 :: 
  { Set_Union_4497(a, b) } { Set_Intersection_4497(a, b) } 
  Set_Size_4497(Set_Union_4497(a, b)) + Set_Size_4497(Set_Intersection_4497(a, b))
     == Set_Size_4497(a) + Set_Size_4497(b));

axiom (forall a: [int]bool :: 
  { Choice_1488(a) } 
  a == MapConst_5_1529(false) || a[Choice_1488(a)]);

axiom (forall a: [Permission]bool :: 
  { Choice_3570(a) } 
  a == MapConst_5_3570(false) || a[Choice_3570(a)]);

function {:builtin "MapConst"} MapConst_3_4497(int) : [Permission]int;

function {:builtin "MapEq"} MapEq_4497_3([Permission]int, [Permission]int) : [Permission]bool;

function {:builtin "MapAdd"} MapAdd_4497([Permission]int, [Permission]int) : [Permission]int;

function {:builtin "MapIte"} MapIte_4497_3([Permission]bool, [Permission]int, [Permission]int) : [Permission]int;

function {:builtin "MapLe"} MapLe_4497([Permission]int, [Permission]int) : [Permission]bool;

function {:inline} Set_Collector_4497(a: Set_4497) : [Permission]bool
{
  a->val
}

function {:inline} One_Collector_4830(a: One_4830) : [Permission]bool
{
  MapOne_4830(a->val)
}

function {:inline} MapOne_4830(t: Permission) : [Permission]bool
{
  MapConst_5_3570(false)[t := true]
}

function {:inline} Collector_read_f_Permission(target: read_f) : [Permission]bool
{
  (if target is read_f
     then MapOr_4497(One_Collector_4830(target->perm), MapConst_5_3570(false))
     else MapConst_5_3570(false))
}

function {:builtin "MapAdd"} MapAdd_9215([atomic_main_f]int, [atomic_main_f]int) : [atomic_main_f]int;

function {:builtin "MapConst"} MapConst_3_9226(int) : [atomic_main_f]int;

function {:builtin "MapIte"} MapIte_9233_3([atomic_main_f]bool, [atomic_main_f]int, [atomic_main_f]int)
   : [atomic_main_f]int;

function {:builtin "MapAdd"} MapAdd_9247([read_f]int, [read_f]int) : [read_f]int;

function {:builtin "MapConst"} MapConst_3_9258(int) : [read_f]int;

function {:builtin "MapIte"} MapIte_9265_3([read_f]bool, [read_f]int, [read_f]int) : [read_f]int;

function {:builtin "MapAdd"} MapAdd_9279([atomic_main_s]int, [atomic_main_s]int) : [atomic_main_s]int;

function {:builtin "MapConst"} MapConst_3_9290(int) : [atomic_main_s]int;

function {:builtin "MapIte"} MapIte_9297_3([atomic_main_s]bool, [atomic_main_s]int, [atomic_main_s]int)
   : [atomic_main_s]int;

datatype Choice_Inv_f {
  Choice_Inv_f_read_f(read_f: read_f)
}

function Trigger_main_f'_sps2(sps2: Set_4497) : bool;

function Trigger_main_f'_done_set(done_set: Set_4497) : bool;

function Trigger_read_f_k(k: int) : bool;

function Trigger_read_f_v(v: Value) : bool;

function Trigger_write_x(x: StampedValue) : bool;

function Trigger_Inv_f_j(j: int) : bool;

function Trigger_Inv_f_sps2(sps2: Set_4497) : bool;

function Trigger_Inv_f_done_set(done_set: Set_4497) : bool;

function Trigger_Inv_f_choice(choice: read_f) : bool;

implementation atomic_get_permissions(tid: Tid) returns (sps: Set_4497)
{
  /*** structured program:
    call sps := Set_Get_3567(pSet, (lambda x: Permission :: 
      x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
  **** end structured program */

  anon0:
    sps := Set_4497((lambda x: Permission :: 
        x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
    pSet := Set_Difference_4497(pSet, sps);
    return;
}



procedure {:inline 1} atomic_get_permissions(tid: Tid) returns (sps: Set_4497);
  modifies pSet;



function {:inline} Civl_InputOutputRelation_atomic_get_permissions(tid: Tid, sps: Set_4497) : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_r1: [Tid][int]StampedValue, 
      Civl_old_r2: [Tid][int]StampedValue, 
      Civl_old_pSet: Set_4497, 
      Civl_old_done_first: bool, 
      Civl_old_done_second: bool, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4497, 
      Civl_done_first: bool, 
      Civl_done_second: bool :: 
    Set_IsSubset_3570(Set_4497((lambda x: Permission :: 
            x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n)), 
        Civl_old_pSet)
       && 
      sps
         == Set_4497((lambda x: Permission :: 
            x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n))
       && Civl_pSet == Set_Difference_4497(Civl_old_pSet, sps))
}

implementation atomic_check_first()
{
  /*** structured program:
    assume done_first;
  **** end structured program */

  anon0:
    assume done_first;
    return;
}



procedure {:inline 1} atomic_check_first();



function {:inline} Civl_InputOutputRelation_atomic_check_first() : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_r1: [Tid][int]StampedValue, 
      Civl_old_r2: [Tid][int]StampedValue, 
      Civl_old_pSet: Set_4497, 
      Civl_old_done_first: bool, 
      Civl_old_done_second: bool, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4497, 
      Civl_done_first: bool, 
      Civl_done_second: bool :: 
    Civl_done_first)
}

implementation atomic_check_second()
{
  /*** structured program:
    assume done_second;
  **** end structured program */

  anon0:
    assume done_second;
    return;
}



procedure {:inline 1} atomic_check_second();



function {:inline} Civl_InputOutputRelation_atomic_check_second() : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_r1: [Tid][int]StampedValue, 
      Civl_old_r2: [Tid][int]StampedValue, 
      Civl_old_pSet: Set_4497, 
      Civl_old_done_first: bool, 
      Civl_old_done_second: bool, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4497, 
      Civl_done_first: bool, 
      Civl_done_second: bool :: 
    Civl_done_second)
}

implementation main_f'(tid: Tid, sps: Set_4497)
{
  var sps2: Set_4497;
  var done_set: Set_4497;

  /*** structured program:
    sps2 := sps;
    assume {:add_to_pool "A", 0, n} true;
    assert sps
       == Set_4497((lambda x: Permission :: 
          x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
    havoc r1;
    assume (forall i: int :: 
      1 <= i && i <= n ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i]);
    call done_set := Set_Get_3567(sps2, (lambda x: Permission :: 
      x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
    call Set_Put_3567(pSet, done_set);
    done_first := true;
  **** end structured program */

  anon0:
    sps2 := sps;
    assume {:add_to_pool "A", 0, n} true;
    havoc r1;
    assume (forall i: int :: 
      1 <= i && i <= n ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i]);
    done_set := Set_4497((lambda x: Permission :: 
        x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
    sps2 := Set_Difference_4497(sps2, done_set);
    pSet := Set_Union_4497(pSet, done_set);
    done_first := true;
    return;
}



procedure {:inline 1} main_f'(tid: Tid, sps: Set_4497);
  modifies r1, pSet, done_first;



function {:inline} Civl_InputOutputRelation_main_f'(tid: Tid, sps: Set_4497) : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_r1: [Tid][int]StampedValue, 
      Civl_old_r2: [Tid][int]StampedValue, 
      Civl_old_pSet: Set_4497, 
      Civl_old_done_first: bool, 
      Civl_old_done_second: bool, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4497, 
      Civl_done_first: bool, 
      Civl_done_second: bool :: 
    (true
         ==> (forall r1: [Tid][int]StampedValue :: 
          (forall i: int :: 
              1 <= i && i <= n
                 ==> r1[tid][i]->ts < Civl_old_mem[i]->ts || r1[tid][i] == Civl_old_mem[i])
             ==> Set_IsSubset_3570(Set_4497((lambda x: Permission :: 
                  x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n)), 
              sps)))
       && (true
         ==> sps
           == Set_4497((lambda x: Permission :: 
              x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n)))
       && 
      true
       && (forall i: int :: 
        1 <= i && i <= n
           ==> Civl_r1[tid][i]->ts < Civl_mem[i]->ts || Civl_r1[tid][i] == Civl_mem[i])
       && Civl_pSet
         == Set_Union_4497(Civl_old_pSet, 
          Set_4497((lambda x: Permission :: 
              x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n)))
       && (Civl_done_first <==> true))
}

implementation read_f(perm: One_4830)
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

    call One_Put_3567(pSet, perm);
    if (Set_IsSubset(WholeTidPermission(perm->val->t_id), pSet))
    {
        done_first := true;
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
    pSet := Set_Add_3567(pSet, perm->val);
    goto anon6_Then, anon6_Else;

  anon6_Else:
    assume {:partition} !Set_IsSubset_3570(WholeTidPermission(perm->val->t_id), pSet);
    return;

  anon6_Then:
    assume {:partition} Set_IsSubset_3570(WholeTidPermission(perm->val->t_id), pSet);
    done_first := true;
    return;

  anon5_Then:
    assume {:add_to_pool "K", mem[perm->val->mem_index]->ts, k} {:add_to_pool "V", mem[perm->val->mem_index]->value, v} true;
    assume k < mem[perm->val->mem_index]->ts;
    r1[perm->val->t_id][perm->val->mem_index] := StampedValue(k, v);
    goto anon3;
}



procedure {:inline 1} read_f(perm: One_4830);
  modifies r1, pSet, done_first;



function {:inline} Civl_InputOutputRelation_read_f(perm: One_4830) : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_r1: [Tid][int]StampedValue, 
      Civl_old_r2: [Tid][int]StampedValue, 
      Civl_old_pSet: Set_4497, 
      Civl_old_done_first: bool, 
      Civl_old_done_second: bool, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4497, 
      Civl_done_first: bool, 
      Civl_done_second: bool :: 
    1 <= perm->val->mem_index
       && perm->val->mem_index <= n
       && (
        (exists {:pool "K"} Civl_k#0: int, {:pool "V"} Civl_v#0: Value :: 
          true
             && true
             && Civl_k#0 < Civl_mem[perm->val->mem_index]->ts
             && Set_IsSubset_3570(WholeTidPermission(perm->val->t_id), Civl_pSet)
             && Civl_r1
               == Civl_old_r1[perm->val->t_id := Civl_old_r1[perm->val->t_id][perm->val->mem_index := StampedValue(Civl_k#0, Civl_v#0)]]
             && Civl_pSet == Set_Add_3567(Civl_old_pSet, perm->val)
             && (Civl_done_first <==> true))
         || (exists {:pool "K"} Civl_k#0: int, {:pool "V"} Civl_v#0: Value :: 
          true
             && true
             && Civl_k#0 < Civl_mem[perm->val->mem_index]->ts
             && !Set_IsSubset_3570(WholeTidPermission(perm->val->t_id), Civl_pSet)
             && Civl_r1
               == Civl_old_r1[perm->val->t_id := Civl_old_r1[perm->val->t_id][perm->val->mem_index := StampedValue(Civl_k#0, Civl_v#0)]]
             && Civl_pSet == Set_Add_3567(Civl_old_pSet, perm->val)
             && (Civl_done_first <==> Civl_old_done_first))
         || (
          true
           && Set_IsSubset_3570(WholeTidPermission(perm->val->t_id), Civl_pSet)
           && Civl_r1
             == Civl_old_r1[perm->val->t_id := Civl_old_r1[perm->val->t_id][perm->val->mem_index := Civl_mem[perm->val->mem_index]]]
           && Civl_pSet == Set_Add_3567(Civl_old_pSet, perm->val)
           && (Civl_done_first <==> true))
         || (
          true
           && !Set_IsSubset_3570(WholeTidPermission(perm->val->t_id), Civl_pSet)
           && Civl_r1
             == Civl_old_r1[perm->val->t_id := Civl_old_r1[perm->val->t_id][perm->val->mem_index := Civl_mem[perm->val->mem_index]]]
           && Civl_pSet == Set_Add_3567(Civl_old_pSet, perm->val)
           && (Civl_done_first <==> Civl_old_done_first))))
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
      Civl_old_pSet: Set_4497, 
      Civl_old_done_first: bool, 
      Civl_old_done_second: bool, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4497, 
      Civl_done_first: bool, 
      Civl_done_second: bool :: 
    Civl_mem == Civl_old_mem[i := StampedValue(Civl_old_mem[i]->ts + 1, v)])
}

implementation Inv_f(tid: Tid, sps: Set_4497) returns (Civl_PAs_read_f: [read_f]int)
{
  var {:pool "A"} j: int;
  var sps2: Set_4497;
  var done_set: Set_4497;
  var choice: read_f;

  /*** structured program:
    sps2 := sps;
    assert sps == WholeTidPermission(tid);
    assume {:add_to_pool "A", 0, j + 1, n} 0 <= j && j <= n;
    havoc r1;
    assume (forall i: int :: 
      1 <= i && i <= j ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i]);
    assume {:add_to_pool "D", Permission(tid, n)} true;
    call done_set := Set_Get_3567(sps2, (lambda {:pool "D"} x: Permission :: 
      x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j));
    call Set_Put_3567(pSet, done_set);
    if (j < n)
    {
        choice := read_f(One_4830(Permission(tid, j + 1)));
        assume {:add_to_pool "C", choice} true;
        call create_asyncs((lambda {:pool "C"} pa: read_f :: 
          j + 1 <= pa->perm->val->mem_index
             && pa->perm->val->mem_index <= n
             && pa->perm->val->t_id == tid));
        call set_choice(choice);
    }
    else
    {
        done_first := true;
    }
  **** end structured program */

  anon0:
    assume Trigger_Inv_f_j(j);
    Civl_PAs_read_f := MapConst_3_9258(0);
    sps2 := sps;
    assume {:add_to_pool "A", 0, j + 1, n} 0 <= j && j <= n;
    havoc r1;
    assume (forall i: int :: 
      1 <= i && i <= j ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i]);
    assume {:add_to_pool "D", Permission(tid, n)} true;
    done_set := Set_4497((lambda {:pool "D"} x: Permission :: 
        x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j));
    sps2 := Set_Difference_4497(sps2, done_set);
    pSet := Set_Union_4497(pSet, done_set);
    goto anon3_Then, anon3_Else;

  anon3_Else:
    assume {:partition} n <= j;
    done_first := true;
    return;

  anon3_Then:
    assume {:partition} j < n;
    choice := read_f(One_4830(Permission(tid, j + 1)));
    assume {:add_to_pool "C", choice} true;
    Civl_PAs_read_f := MapAdd_9247(Civl_PAs_read_f, 
      MapIte_9265_3((lambda {:pool "C"} pa: read_f :: 
          j + 1 <= pa->perm->val->mem_index
             && pa->perm->val->mem_index <= n
             && pa->perm->val->t_id == tid), 
        MapConst_3_9258(1), 
        MapConst_3_9258(0)));
    return;
}



procedure {:inline 1} Inv_f(tid: Tid, sps: Set_4497) returns (Civl_PAs_read_f: [read_f]int);
  modifies r1, pSet, done_first;



function {:inline} Civl_InputOutputRelation_Inv_f(tid: Tid, sps: Set_4497, Civl_PAs_read_f: [read_f]int) : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_r1: [Tid][int]StampedValue, 
      Civl_old_r2: [Tid][int]StampedValue, 
      Civl_old_pSet: Set_4497, 
      Civl_old_done_first: bool, 
      Civl_old_done_second: bool, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4497, 
      Civl_done_first: bool, 
      Civl_done_second: bool :: 
    (forall j: int :: 
        0 <= j && j <= n
           ==> (forall r1: [Tid][int]StampedValue :: 
            (forall i: int :: 
                1 <= i && i <= j
                   ==> r1[tid][i]->ts < Civl_old_mem[i]->ts || r1[tid][i] == Civl_old_mem[i])
               ==> 
              true
               ==> Set_IsSubset_3570(Set_4497((lambda {:pool "D"} x: Permission :: 
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
             && Civl_pSet
               == Set_Union_4497(Civl_old_pSet, 
                Set_4497((lambda {:pool "D"} x: Permission :: 
                    x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
             && Civl_PAs_read_f
               == MapAdd_9247(MapConst_3_9258(0), 
                MapIte_9265_3((lambda {:pool "C"} pa: read_f :: 
                    Civl_j#0 + 1 <= pa->perm->val->mem_index
                       && pa->perm->val->mem_index <= n
                       && pa->perm->val->t_id == tid), 
                  MapConst_3_9258(1), 
                  MapConst_3_9258(0)))
             && (Civl_done_first <==> Civl_old_done_first))
         || (exists {:pool "A"} Civl_j#0: int :: 
          0 <= Civl_j#0
             && Civl_j#0 <= n
             && (forall i: int :: 
              1 <= i && i <= Civl_j#0
                 ==> Civl_r1[tid][i]->ts < Civl_mem[i]->ts || Civl_r1[tid][i] == Civl_mem[i])
             && true
             && n <= Civl_j#0
             && Civl_PAs_read_f == MapConst_3_9258(0)
             && Civl_pSet
               == Set_Union_4497(Civl_old_pSet, 
                Set_4497((lambda {:pool "D"} x: Permission :: 
                    x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
             && (Civl_done_first <==> true))))
}

implementation Inv_f_With_Choice(tid: Tid, sps: Set_4497)
   returns (Civl_PAs_read_f: [read_f]int, Civl_choice: Choice_Inv_f)
{
  var {:pool "A"} j: int;
  var sps2: Set_4497;
  var done_set: Set_4497;
  var choice: read_f;

  /*** structured program:
    sps2 := sps;
    assert sps == WholeTidPermission(tid);
    assume {:add_to_pool "A", 0, j + 1, n} 0 <= j && j <= n;
    havoc r1;
    assume (forall i: int :: 
      1 <= i && i <= j ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i]);
    assume {:add_to_pool "D", Permission(tid, n)} true;
    call done_set := Set_Get_3567(sps2, (lambda {:pool "D"} x: Permission :: 
      x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j));
    call Set_Put_3567(pSet, done_set);
    if (j < n)
    {
        choice := read_f(One_4830(Permission(tid, j + 1)));
        assume {:add_to_pool "C", choice} true;
        call create_asyncs((lambda {:pool "C"} pa: read_f :: 
          j + 1 <= pa->perm->val->mem_index
             && pa->perm->val->mem_index <= n
             && pa->perm->val->t_id == tid));
        call set_choice(choice);
    }
    else
    {
        done_first := true;
    }
  **** end structured program */

  anon0:
    Civl_PAs_read_f := MapConst_3_9258(0);
    sps2 := sps;
    assert sps == WholeTidPermission(tid);
    assume {:add_to_pool "A", 0, j + 1, n} 0 <= j && j <= n;
    havoc r1;
    assume (forall i: int :: 
      1 <= i && i <= j ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i]);
    assume {:add_to_pool "D", Permission(tid, n)} true;
    done_set := Set_4497((lambda {:pool "D"} x: Permission :: 
        x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j));
    assert Set_IsSubset_3570(done_set, sps2);
    sps2 := Set_Difference_4497(sps2, done_set);
    pSet := Set_Union_4497(pSet, done_set);
    goto anon3_Then, anon3_Else;

  anon3_Else:
    assume {:partition} n <= j;
    done_first := true;
    return;

  anon3_Then:
    assume {:partition} j < n;
    choice := read_f(One_4830(Permission(tid, j + 1)));
    assume {:add_to_pool "C", choice} true;
    Civl_PAs_read_f := MapAdd_9247(Civl_PAs_read_f, 
      MapIte_9265_3((lambda {:pool "C"} pa: read_f :: 
          j + 1 <= pa->perm->val->mem_index
             && pa->perm->val->mem_index <= n
             && pa->perm->val->t_id == tid), 
        MapConst_3_9258(1), 
        MapConst_3_9258(0)));
    assert Civl_PAs_read_f == MapConst_3_9258(0) || Civl_PAs_read_f[choice] > 0;
    Civl_choice->read_f := choice;
    return;
}



procedure {:inline 1} Inv_f_With_Choice(tid: Tid, sps: Set_4497)
   returns (Civl_PAs_read_f: [read_f]int, Civl_choice: Choice_Inv_f);
  modifies r1, pSet, done_first;



function {:inline} Civl_InputOutputRelation_Inv_f_With_Choice(tid: Tid, sps: Set_4497, Civl_PAs_read_f: [read_f]int, Civl_choice: Choice_Inv_f)
   : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_r1: [Tid][int]StampedValue, 
      Civl_old_r2: [Tid][int]StampedValue, 
      Civl_old_pSet: Set_4497, 
      Civl_old_done_first: bool, 
      Civl_old_done_second: bool, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4497, 
      Civl_done_first: bool, 
      Civl_done_second: bool :: 
    (forall j: int :: 
        0 <= j && j <= n
           ==> (forall r1: [Tid][int]StampedValue :: 
            (forall i: int :: 
                1 <= i && i <= j
                   ==> r1[tid][i]->ts < Civl_old_mem[i]->ts || r1[tid][i] == Civl_old_mem[i])
               ==> 
              true
               ==> Set_IsSubset_3570(Set_4497((lambda {:pool "D"} x: Permission :: 
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
             && Set_IsSubset_3570(Set_4497((lambda {:pool "D"} x: Permission :: 
                  x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)), 
              sps)
             && Civl_j#0 < n
             && true
             && (Civl_PAs_read_f == MapConst_3_9258(0)
               || Civl_PAs_read_f[read_f(One_4830(Permission(tid, Civl_j#0 + 1)))] > 0)
             && Civl_pSet
               == Set_Union_4497(Civl_old_pSet, 
                Set_4497((lambda {:pool "D"} x: Permission :: 
                    x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
             && Civl_PAs_read_f
               == MapAdd_9247(MapConst_3_9258(0), 
                MapIte_9265_3((lambda {:pool "C"} pa: read_f :: 
                    Civl_j#0 + 1 <= pa->perm->val->mem_index
                       && pa->perm->val->mem_index <= n
                       && pa->perm->val->t_id == tid), 
                  MapConst_3_9258(1), 
                  MapConst_3_9258(0)))
             && Civl_choice
               == Choice_Inv_f_read_f(read_f(One_4830(Permission(tid, Civl_j#0 + 1))))
             && (Civl_done_first <==> Civl_old_done_first))
         || (exists {:pool "A"} Civl_j#0: int :: 
          sps == WholeTidPermission(tid)
             && 0 <= Civl_j#0
             && Civl_j#0 <= n
             && (forall i: int :: 
              1 <= i && i <= Civl_j#0
                 ==> Civl_r1[tid][i]->ts < Civl_mem[i]->ts || Civl_r1[tid][i] == Civl_mem[i])
             && true
             && Set_IsSubset_3570(Set_4497((lambda {:pool "D"} x: Permission :: 
                  x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)), 
              sps)
             && n <= Civl_j#0
             && Civl_PAs_read_f == MapConst_3_9258(0)
             && Civl_pSet
               == Set_Union_4497(Civl_old_pSet, 
                Set_4497((lambda {:pool "D"} x: Permission :: 
                    x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
             && (Civl_done_first <==> true))))
}

implementation atomic_main_s(tid: Tid, sps: Set_4497) returns (Civl_PAs_read_f: [read_f]int)
{
  /*** structured program:
    assume {:add_to_pool "A", 0, n} true;
    assert sps
       == Set_4497((lambda x: Permission :: 
          x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
    call create_asyncs_3602((lambda pa: read_f :: 
      1 <= pa->perm->val->mem_index
         && pa->perm->val->mem_index <= n
         && pa->perm->val->t_id == tid));
  **** end structured program */

  anon0:
    Civl_PAs_read_f := MapConst_3_9258(0);
    assume {:add_to_pool "A", 0, n} true;
    Civl_PAs_read_f := MapAdd_9247(Civl_PAs_read_f, 
      MapIte_9265_3((lambda pa: read_f :: 
          1 <= pa->perm->val->mem_index
             && pa->perm->val->mem_index <= n
             && pa->perm->val->t_id == tid), 
        MapConst_3_9258(1), 
        MapConst_3_9258(0)));
    return;
}



procedure {:inline 1} atomic_main_s(tid: Tid, sps: Set_4497) returns (Civl_PAs_read_f: [read_f]int);



function {:inline} Civl_InputOutputRelation_atomic_main_s(tid: Tid, sps: Set_4497, Civl_PAs_read_f: [read_f]int) : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_r1: [Tid][int]StampedValue, 
      Civl_old_r2: [Tid][int]StampedValue, 
      Civl_old_pSet: Set_4497, 
      Civl_old_done_first: bool, 
      Civl_old_done_second: bool, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4497, 
      Civl_done_first: bool, 
      Civl_done_second: bool :: 
    (true
         ==> sps
           == Set_4497((lambda x: Permission :: 
              x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n)))
       && 
      true
       && Civl_PAs_read_f
         == MapAdd_9247(MapConst_3_9258(0), 
          MapIte_9265_3((lambda pa: read_f :: 
              1 <= pa->perm->val->mem_index
                 && pa->perm->val->mem_index <= n
                 && pa->perm->val->t_id == tid), 
            MapConst_3_9258(1), 
            MapConst_3_9258(0))))
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
      Civl_old_r1: [Tid][int]StampedValue, 
      Civl_old_r2: [Tid][int]StampedValue, 
      Civl_old_pSet: Set_4497, 
      Civl_old_done_first: bool, 
      Civl_old_done_second: bool, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4497, 
      Civl_done_first: bool, 
      Civl_done_second: bool :: 
    true)
}

implementation atomic_main_f(tid: Tid, sps: Set_4497) returns (Civl_PAs_read_f: [read_f]int)
{
  /*** structured program:
    assume {:add_to_pool "A", 0, n} true;
    assert sps
       == Set_4497((lambda x: Permission :: 
          x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
    call create_asyncs_3602((lambda pa: read_f :: 
      1 <= pa->perm->val->mem_index
         && pa->perm->val->mem_index <= n
         && pa->perm->val->t_id == tid));
  **** end structured program */

  anon0:
    Civl_PAs_read_f := MapConst_3_9258(0);
    assume {:add_to_pool "A", 0, n} true;
    Civl_PAs_read_f := MapAdd_9247(Civl_PAs_read_f, 
      MapIte_9265_3((lambda pa: read_f :: 
          1 <= pa->perm->val->mem_index
             && pa->perm->val->mem_index <= n
             && pa->perm->val->t_id == tid), 
        MapConst_3_9258(1), 
        MapConst_3_9258(0)));
    return;
}



procedure {:inline 1} atomic_main_f(tid: Tid, sps: Set_4497) returns (Civl_PAs_read_f: [read_f]int);



function {:inline} Civl_InputOutputRelation_atomic_main_f(tid: Tid, sps: Set_4497, Civl_PAs_read_f: [read_f]int) : bool
{
  (exists Civl_old_mem: [int]StampedValue, 
      Civl_old_r1: [Tid][int]StampedValue, 
      Civl_old_r2: [Tid][int]StampedValue, 
      Civl_old_pSet: Set_4497, 
      Civl_old_done_first: bool, 
      Civl_old_done_second: bool, 
      Civl_mem: [int]StampedValue, 
      Civl_r1: [Tid][int]StampedValue, 
      Civl_r2: [Tid][int]StampedValue, 
      Civl_pSet: Set_4497, 
      Civl_done_first: bool, 
      Civl_done_second: bool :: 
    (true
         ==> sps
           == Set_4497((lambda x: Permission :: 
              x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n)))
       && 
      true
       && Civl_PAs_read_f
         == MapAdd_9247(MapConst_3_9258(0), 
          MapIte_9265_3((lambda pa: read_f :: 
              1 <= pa->perm->val->mem_index
                 && pa->perm->val->mem_index <= n
                 && pa->perm->val->t_id == tid), 
            MapConst_3_9258(1), 
            MapConst_3_9258(0))))
}

implementation Civl_CommutativityChecker_read_f_atomic_get_permissions_1(first_perm: One_4830, second_tid: Tid) returns (second_sps: Set_4497)
{

  init:
    call read_f(first_perm);
    call second_sps := atomic_get_permissions(second_tid);
    assert (exists Civl_partition_Permission: [Permission]int :: 
        MapImp_3570(Set_Collector_4497(second_sps), 
              MapEq_4497_3(Civl_partition_Permission, MapConst_3_4497(0)))
             == MapConst_5_3570(true)
           && MapImp_3570(Set_Collector_4497(pSet), 
              MapEq_4497_3(Civl_partition_Permission, MapConst_3_4497(1)))
             == MapConst_5_3570(true))
       ==> (exists {:pool "K"} Civl_first_k#0: int, {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && Set_IsSubset_3570(WholeTidPermission(first_perm->val->t_id), pSet)
             && second_sps
               == Set_4497((lambda second_x: Permission :: 
                  second_x->t_id == second_tid
                     && 1 <= second_x->mem_index
                     && second_x->mem_index <= n))
             && r1
               == old(r1)[first_perm->val->t_id := old(r1)[first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet
               == Set_Add_3567(Set_Difference_4497(old(pSet), second_sps), first_perm->val)
             && (done_first <==> true)
             && mem == old(mem))
         || (exists {:pool "K"} Civl_first_k#0: int, {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && !Set_IsSubset_3570(WholeTidPermission(first_perm->val->t_id), pSet)
             && second_sps
               == Set_4497((lambda second_x: Permission :: 
                  second_x->t_id == second_tid
                     && 1 <= second_x->mem_index
                     && second_x->mem_index <= n))
             && r1
               == old(r1)[first_perm->val->t_id := old(r1)[first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet
               == Set_Add_3567(Set_Difference_4497(old(pSet), second_sps), first_perm->val)
             && mem == old(mem)
             && (done_first <==> old(done_first)))
         || (
          true
           && Set_IsSubset_3570(WholeTidPermission(first_perm->val->t_id), pSet)
           && second_sps
             == Set_4497((lambda second_x: Permission :: 
                second_x->t_id == second_tid
                   && 1 <= second_x->mem_index
                   && second_x->mem_index <= n))
           && r1
             == old(r1)[first_perm->val->t_id := old(r1)[first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet
             == Set_Add_3567(Set_Difference_4497(old(pSet), second_sps), first_perm->val)
           && (done_first <==> true)
           && mem == old(mem))
         || (
          true
           && !Set_IsSubset_3570(WholeTidPermission(first_perm->val->t_id), pSet)
           && second_sps
             == Set_4497((lambda second_x: Permission :: 
                second_x->t_id == second_tid
                   && 1 <= second_x->mem_index
                   && second_x->mem_index <= n))
           && r1
             == old(r1)[first_perm->val->t_id := old(r1)[first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet
             == Set_Add_3567(Set_Difference_4497(old(pSet), second_sps), first_perm->val)
           && mem == old(mem)
           && (done_first <==> old(done_first)));
    return;
}



procedure Civl_CommutativityChecker_read_f_atomic_get_permissions_1(first_perm: One_4830, second_tid: Tid) returns (second_sps: Set_4497);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3570(One_Collector_4830(first_perm), 
          MapEq_4497_3(Civl_partition_Permission, MapConst_3_4497(0)))
         == MapConst_5_3570(true)
       && MapImp_3570(Set_Collector_4497(pSet), 
          MapEq_4497_3(Civl_partition_Permission, MapConst_3_4497(1)))
         == MapConst_5_3570(true));
  requires 1 <= first_perm->val->mem_index && first_perm->val->mem_index <= n;
  requires Set_IsSubset_3570(Set_4497((lambda second_x: Permission :: 
        second_x->t_id == second_tid
           && 1 <= second_x->mem_index
           && second_x->mem_index <= n)), 
    pSet);
  requires Set_IsSubset_3570(WholeTidPermission(first_perm->val->t_id), Set_Add_3567(pSet, first_perm->val));
  modifies mem, r1, r2, pSet, done_first, done_second;



implementation Civl_GatePreservationChecker_atomic_get_permissions_read_f_1(first_tid: Tid, second_perm: One_4830) returns (first_sps: Set_4497)
{

  init:
    call read_f(second_perm);
    assert true
       ==> Set_IsSubset_3570(Set_4497((lambda first_x: Permission :: 
            first_x->t_id == first_tid && 1 <= first_x->mem_index && first_x->mem_index <= n)), 
        pSet);
    return;
}



procedure Civl_GatePreservationChecker_atomic_get_permissions_read_f_1(first_tid: Tid, second_perm: One_4830) returns (first_sps: Set_4497);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3570(One_Collector_4830(second_perm), 
          MapEq_4497_3(Civl_partition_Permission, MapConst_3_4497(0)))
         == MapConst_5_3570(true)
       && MapImp_3570(Set_Collector_4497(pSet), 
          MapEq_4497_3(Civl_partition_Permission, MapConst_3_4497(1)))
         == MapConst_5_3570(true));
  requires Set_IsSubset_3570(Set_4497((lambda first_x: Permission :: 
        first_x->t_id == first_tid && 1 <= first_x->mem_index && first_x->mem_index <= n)), 
    pSet);
  requires 1 <= second_perm->val->mem_index && second_perm->val->mem_index <= n;
  requires Set_IsSubset_3570(WholeTidPermission(second_perm->val->t_id), Set_Add_3567(pSet, second_perm->val));
  modifies mem, r1, r2, pSet, done_first, done_second;



implementation Civl_CommutativityChecker_read_f_atomic_check_first_1(first_perm: One_4830)
{

  init:
    call read_f(first_perm);
    call atomic_check_first();
    assert true
       ==> (exists {:pool "K"} Civl_first_k#0: int, {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_first_v#0) } 
          old(done_first)
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && Set_IsSubset_3570(WholeTidPermission(first_perm->val->t_id), pSet)
             && r1
               == old(r1)[first_perm->val->t_id := old(r1)[first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3567(old(pSet), first_perm->val)
             && (done_first <==> true)
             && mem == old(mem))
         || (exists {:pool "K"} Civl_first_k#0: int, {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_first_v#0) } 
          done_first
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && !Set_IsSubset_3570(WholeTidPermission(first_perm->val->t_id), pSet)
             && r1
               == old(r1)[first_perm->val->t_id := old(r1)[first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3567(old(pSet), first_perm->val)
             && mem == old(mem)
             && (done_first <==> old(done_first)))
         || (
          old(done_first)
           && true
           && Set_IsSubset_3570(WholeTidPermission(first_perm->val->t_id), pSet)
           && r1
             == old(r1)[first_perm->val->t_id := old(r1)[first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet == Set_Add_3567(old(pSet), first_perm->val)
           && (done_first <==> true)
           && mem == old(mem))
         || (
          done_first
           && true
           && !Set_IsSubset_3570(WholeTidPermission(first_perm->val->t_id), pSet)
           && r1
             == old(r1)[first_perm->val->t_id := old(r1)[first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet == Set_Add_3567(old(pSet), first_perm->val)
           && mem == old(mem)
           && (done_first <==> old(done_first)));
    return;
}



procedure Civl_CommutativityChecker_read_f_atomic_check_first_1(first_perm: One_4830);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3570(One_Collector_4830(first_perm), 
          MapEq_4497_3(Civl_partition_Permission, MapConst_3_4497(0)))
         == MapConst_5_3570(true)
       && MapImp_3570(Set_Collector_4497(pSet), 
          MapEq_4497_3(Civl_partition_Permission, MapConst_3_4497(1)))
         == MapConst_5_3570(true));
  requires 1 <= first_perm->val->mem_index && first_perm->val->mem_index <= n;
  requires Set_IsSubset_3570(WholeTidPermission(first_perm->val->t_id), Set_Add_3567(pSet, first_perm->val));
  modifies mem, r1, r2, pSet, done_first, done_second;



implementation Civl_CommutativityChecker_read_f_read_f_1(first_perm: One_4830, second_perm: One_4830)
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
             && Set_IsSubset_3570(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3567(old(pSet), second_perm->val))
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && Set_IsSubset_3570(WholeTidPermission(first_perm->val->t_id), pSet)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3567(Set_Add_3567(old(pSet), second_perm->val), first_perm->val)
             && (done_first <==> true)
             && mem == old(mem))
         || (exists {:pool "K"} Civl_second_k#0: int, 
            {:pool "K"} Civl_first_k#0: int, 
            {:pool "V"} Civl_second_v#0: Value, 
            {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_second_v#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && Set_IsSubset_3570(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3567(old(pSet), second_perm->val))
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && !Set_IsSubset_3570(WholeTidPermission(first_perm->val->t_id), pSet)
             && (done_first <==> true)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3567(Set_Add_3567(old(pSet), second_perm->val), first_perm->val)
             && mem == old(mem))
         || (exists {:pool "K"} Civl_second_k#0: int, {:pool "V"} Civl_second_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_v(Civl_second_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && Set_IsSubset_3570(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3567(old(pSet), second_perm->val))
             && true
             && Set_IsSubset_3570(WholeTidPermission(first_perm->val->t_id), pSet)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
             && pSet == Set_Add_3567(Set_Add_3567(old(pSet), second_perm->val), first_perm->val)
             && (done_first <==> true)
             && mem == old(mem))
         || (exists {:pool "K"} Civl_second_k#0: int, {:pool "V"} Civl_second_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_v(Civl_second_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && Set_IsSubset_3570(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3567(old(pSet), second_perm->val))
             && true
             && !Set_IsSubset_3570(WholeTidPermission(first_perm->val->t_id), pSet)
             && (done_first <==> true)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
             && pSet == Set_Add_3567(Set_Add_3567(old(pSet), second_perm->val), first_perm->val)
             && mem == old(mem))
         || (exists {:pool "K"} Civl_second_k#0: int, 
            {:pool "K"} Civl_first_k#0: int, 
            {:pool "V"} Civl_second_v#0: Value, 
            {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_second_v#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && !Set_IsSubset_3570(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3567(old(pSet), second_perm->val))
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && Set_IsSubset_3570(WholeTidPermission(first_perm->val->t_id), pSet)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3567(Set_Add_3567(old(pSet), second_perm->val), first_perm->val)
             && (done_first <==> true)
             && mem == old(mem))
         || (exists {:pool "K"} Civl_second_k#0: int, 
            {:pool "K"} Civl_first_k#0: int, 
            {:pool "V"} Civl_second_v#0: Value, 
            {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_second_v#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && !Set_IsSubset_3570(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3567(old(pSet), second_perm->val))
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && !Set_IsSubset_3570(WholeTidPermission(first_perm->val->t_id), pSet)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3567(Set_Add_3567(old(pSet), second_perm->val), first_perm->val)
             && mem == old(mem)
             && (done_first <==> old(done_first)))
         || (exists {:pool "K"} Civl_second_k#0: int, {:pool "V"} Civl_second_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_v(Civl_second_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && !Set_IsSubset_3570(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3567(old(pSet), second_perm->val))
             && true
             && Set_IsSubset_3570(WholeTidPermission(first_perm->val->t_id), pSet)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
             && pSet == Set_Add_3567(Set_Add_3567(old(pSet), second_perm->val), first_perm->val)
             && (done_first <==> true)
             && mem == old(mem))
         || (exists {:pool "K"} Civl_second_k#0: int, {:pool "V"} Civl_second_v#0: Value :: 
          { Trigger_read_f_k(Civl_second_k#0), Trigger_read_f_v(Civl_second_v#0) } 
          true
             && true
             && Civl_second_k#0 < mem[second_perm->val->mem_index]->ts
             && !Set_IsSubset_3570(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3567(old(pSet), second_perm->val))
             && true
             && !Set_IsSubset_3570(WholeTidPermission(first_perm->val->t_id), pSet)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := StampedValue(Civl_second_k#0, Civl_second_v#0)]][first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
             && pSet == Set_Add_3567(Set_Add_3567(old(pSet), second_perm->val), first_perm->val)
             && mem == old(mem)
             && (done_first <==> old(done_first)))
         || (exists {:pool "K"} Civl_first_k#0: int, {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && Set_IsSubset_3570(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3567(old(pSet), second_perm->val))
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && Set_IsSubset_3570(WholeTidPermission(first_perm->val->t_id), pSet)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3567(Set_Add_3567(old(pSet), second_perm->val), first_perm->val)
             && (done_first <==> true)
             && mem == old(mem))
         || (exists {:pool "K"} Civl_first_k#0: int, {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && Set_IsSubset_3570(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3567(old(pSet), second_perm->val))
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && !Set_IsSubset_3570(WholeTidPermission(first_perm->val->t_id), pSet)
             && (done_first <==> true)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3567(Set_Add_3567(old(pSet), second_perm->val), first_perm->val)
             && mem == old(mem))
         || (
          true
           && Set_IsSubset_3570(WholeTidPermission(second_perm->val->t_id), 
            Set_Add_3567(old(pSet), second_perm->val))
           && true
           && Set_IsSubset_3570(WholeTidPermission(first_perm->val->t_id), pSet)
           && r1
             == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet == Set_Add_3567(Set_Add_3567(old(pSet), second_perm->val), first_perm->val)
           && (done_first <==> true)
           && mem == old(mem))
         || (
          true
           && Set_IsSubset_3570(WholeTidPermission(second_perm->val->t_id), 
            Set_Add_3567(old(pSet), second_perm->val))
           && true
           && !Set_IsSubset_3570(WholeTidPermission(first_perm->val->t_id), pSet)
           && (done_first <==> true)
           && r1
             == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet == Set_Add_3567(Set_Add_3567(old(pSet), second_perm->val), first_perm->val)
           && mem == old(mem))
         || (exists {:pool "K"} Civl_first_k#0: int, {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && !Set_IsSubset_3570(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3567(old(pSet), second_perm->val))
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && Set_IsSubset_3570(WholeTidPermission(first_perm->val->t_id), pSet)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3567(Set_Add_3567(old(pSet), second_perm->val), first_perm->val)
             && (done_first <==> true)
             && mem == old(mem))
         || (exists {:pool "K"} Civl_first_k#0: int, {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && !Set_IsSubset_3570(WholeTidPermission(second_perm->val->t_id), 
              Set_Add_3567(old(pSet), second_perm->val))
             && true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && !Set_IsSubset_3570(WholeTidPermission(first_perm->val->t_id), pSet)
             && r1
               == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3567(Set_Add_3567(old(pSet), second_perm->val), first_perm->val)
             && mem == old(mem)
             && (done_first <==> old(done_first)))
         || (
          true
           && !Set_IsSubset_3570(WholeTidPermission(second_perm->val->t_id), 
            Set_Add_3567(old(pSet), second_perm->val))
           && true
           && Set_IsSubset_3570(WholeTidPermission(first_perm->val->t_id), pSet)
           && r1
             == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet == Set_Add_3567(Set_Add_3567(old(pSet), second_perm->val), first_perm->val)
           && (done_first <==> true)
           && mem == old(mem))
         || (
          true
           && !Set_IsSubset_3570(WholeTidPermission(second_perm->val->t_id), 
            Set_Add_3567(old(pSet), second_perm->val))
           && true
           && !Set_IsSubset_3570(WholeTidPermission(first_perm->val->t_id), pSet)
           && r1
             == old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id := old(r1)[second_perm->val->t_id := old(r1)[second_perm->val->t_id][second_perm->val->mem_index := mem[second_perm->val->mem_index]]][first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet == Set_Add_3567(Set_Add_3567(old(pSet), second_perm->val), first_perm->val)
           && mem == old(mem)
           && (done_first <==> old(done_first)));
    return;
}



procedure Civl_CommutativityChecker_read_f_read_f_1(first_perm: One_4830, second_perm: One_4830);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3570(One_Collector_4830(first_perm), 
          MapEq_4497_3(Civl_partition_Permission, MapConst_3_4497(0)))
         == MapConst_5_3570(true)
       && MapImp_3570(One_Collector_4830(second_perm), 
          MapEq_4497_3(Civl_partition_Permission, MapConst_3_4497(1)))
         == MapConst_5_3570(true)
       && MapImp_3570(Set_Collector_4497(pSet), 
          MapEq_4497_3(Civl_partition_Permission, MapConst_3_4497(2)))
         == MapConst_5_3570(true));
  requires 1 <= first_perm->val->mem_index && first_perm->val->mem_index <= n;
  requires 1 <= second_perm->val->mem_index && second_perm->val->mem_index <= n;
  requires Set_IsSubset_3570(WholeTidPermission(first_perm->val->t_id), Set_Add_3567(pSet, first_perm->val));
  modifies mem, r1, r2, pSet, done_first, done_second;



implementation Civl_CommutativityChecker_read_f_write_1(first_perm: One_4830, second_i: int, second_v: Value)
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
             && Set_IsSubset_3570(WholeTidPermission(first_perm->val->t_id), pSet)
             && mem == old(mem)[second_i := StampedValue(old(mem)[second_i]->ts + 1, second_v)]
             && r1
               == old(r1)[first_perm->val->t_id := old(r1)[first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3567(old(pSet), first_perm->val)
             && (done_first <==> true))
         || (exists {:pool "K"} Civl_first_k#0: int, {:pool "V"} Civl_first_v#0: Value :: 
          { Trigger_read_f_k(Civl_first_k#0), Trigger_read_f_v(Civl_first_v#0) } 
          true
             && true
             && Civl_first_k#0 < mem[first_perm->val->mem_index]->ts
             && !Set_IsSubset_3570(WholeTidPermission(first_perm->val->t_id), pSet)
             && mem == old(mem)[second_i := StampedValue(old(mem)[second_i]->ts + 1, second_v)]
             && r1
               == old(r1)[first_perm->val->t_id := old(r1)[first_perm->val->t_id][first_perm->val->mem_index := StampedValue(Civl_first_k#0, Civl_first_v#0)]]
             && pSet == Set_Add_3567(old(pSet), first_perm->val)
             && (done_first <==> old(done_first)))
         || (
          true
           && Set_IsSubset_3570(WholeTidPermission(first_perm->val->t_id), pSet)
           && mem == old(mem)[second_i := StampedValue(old(mem)[second_i]->ts + 1, second_v)]
           && r1
             == old(r1)[first_perm->val->t_id := old(r1)[first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet == Set_Add_3567(old(pSet), first_perm->val)
           && (done_first <==> true))
         || (
          true
           && !Set_IsSubset_3570(WholeTidPermission(first_perm->val->t_id), pSet)
           && mem == old(mem)[second_i := StampedValue(old(mem)[second_i]->ts + 1, second_v)]
           && r1
             == old(r1)[first_perm->val->t_id := old(r1)[first_perm->val->t_id][first_perm->val->mem_index := mem[first_perm->val->mem_index]]]
           && pSet == Set_Add_3567(old(pSet), first_perm->val)
           && (done_first <==> old(done_first)));
    return;
}



procedure Civl_CommutativityChecker_read_f_write_1(first_perm: One_4830, second_i: int, second_v: Value);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3570(One_Collector_4830(first_perm), 
          MapEq_4497_3(Civl_partition_Permission, MapConst_3_4497(0)))
         == MapConst_5_3570(true)
       && MapImp_3570(Set_Collector_4497(pSet), 
          MapEq_4497_3(Civl_partition_Permission, MapConst_3_4497(1)))
         == MapConst_5_3570(true));
  requires 1 <= first_perm->val->mem_index && first_perm->val->mem_index <= n;
  requires Set_IsSubset_3570(WholeTidPermission(first_perm->val->t_id), Set_Add_3567(pSet, first_perm->val));
  modifies mem, r1, r2, pSet, done_first, done_second;



procedure Civl_coordinator_1(tid: Tid);
  modifies mem, r1, r2, pSet, done_first, done_second;



implementation Civl_coordinator_1(tid: Tid)
{
  var sps: Set_4497;
  var Civl_returnedPAs_read_f: [read_f]int;
  var Civl_global_old_mem: [int]StampedValue;
  var Civl_global_old_r1: [Tid][int]StampedValue;
  var Civl_global_old_r2: [Tid][int]StampedValue;
  var Civl_global_old_pSet: Set_4497;
  var Civl_global_old_done_first: bool;
  var Civl_global_old_done_second: bool;
  var Civl_pc: bool;
  var Civl_ok: bool;
  var Civl_eval: bool;
  var Civl_linear_Permission_available: [Permission]bool;

  /*** structured program:
    assume old(done_first) <==> false;
    call Yield();
    call sps := get_permissions(tid);
    call Yield();
    call main_f(tid, sps);
    call Yield();
    call check_first();
    call Yield();
    call sps := get_permissions(tid);
    call Yield();
    call main_s(tid, sps);
    call Yield();
    call check_second();
  **** end structured program */

  Civl_init:
    havoc mem, r1, r2, pSet, done_first, done_second;
    Civl_global_old_mem, Civl_global_old_r1, Civl_global_old_r2, Civl_global_old_pSet, Civl_global_old_done_first, Civl_global_old_done_second := mem, r1, r2, pSet, done_first, done_second;
    Civl_pc, Civl_ok, Civl_eval := false, false, false;
    assume true;
    Civl_linear_Permission_available := MapOr_4497(Set_Collector_4497(pSet), MapConst_5_3570(false));
    goto anon0;

  anon0:
    assume old(done_first) <==> false;
    Civl_eval := mem == Civl_global_old_mem
       && r1 == Civl_global_old_r1
       && r2 == Civl_global_old_r2
       && pSet == Civl_global_old_pSet
       && (done_first <==> Civl_global_old_done_first)
       && (done_second <==> Civl_global_old_done_second);
    goto anon0_5, Civl_NoninterferenceChecker, Civl_RefinementChecker;

  anon0_5:
    Civl_pc, Civl_ok := mem == Civl_global_old_mem
         && r1 == Civl_global_old_r1
         && r2 == Civl_global_old_r2
         && pSet == Civl_global_old_pSet
         && (done_first <==> Civl_global_old_done_first)
         && (done_second <==> Civl_global_old_done_second)
       ==> Civl_pc, Civl_eval || Civl_ok;
    call Civl_ParallelCall_Yield_1();
    assume Civl_pc || true;
    Civl_global_old_mem, Civl_global_old_r1, Civl_global_old_r2, Civl_global_old_pSet, Civl_global_old_done_first, Civl_global_old_done_second := mem, r1, r2, pSet, done_first, done_second;
    Civl_linear_Permission_available := MapOr_4497(Set_Collector_4497(pSet), MapConst_5_3570(false));
    // <<< injected gate
    assert Set_IsSubset_3570(Set_4497((lambda x: Permission :: 
          x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n)), 
      pSet);
    // injected gate >>>
    call sps := atomic_get_permissions(tid);
    Civl_eval := mem == Civl_global_old_mem
       && r1 == Civl_global_old_r1
       && r2 == Civl_global_old_r2
       && pSet == Civl_global_old_pSet
       && (done_first <==> Civl_global_old_done_first)
       && (done_second <==> Civl_global_old_done_second);
    goto anon0_4, Civl_NoninterferenceChecker, Civl_RefinementChecker;

  anon0_4:
    Civl_pc, Civl_ok := mem == Civl_global_old_mem
         && r1 == Civl_global_old_r1
         && r2 == Civl_global_old_r2
         && pSet == Civl_global_old_pSet
         && (done_first <==> Civl_global_old_done_first)
         && (done_second <==> Civl_global_old_done_second)
       ==> Civl_pc, Civl_eval || Civl_ok;
    call Civl_ParallelCall_Yield_1();
    assume Civl_pc || true;
    Civl_global_old_mem, Civl_global_old_r1, Civl_global_old_r2, Civl_global_old_pSet, Civl_global_old_done_first, Civl_global_old_done_second := mem, r1, r2, pSet, done_first, done_second;
    Civl_linear_Permission_available := MapOr_4497(Set_Collector_4497(pSet), 
      MapOr_4497(Set_Collector_4497(sps), MapConst_5_3570(false)));
    assume (exists Civl_partition_Permission: [Permission]int :: 
      MapImp_3570(Set_Collector_4497(sps), 
            MapEq_4497_3(Civl_partition_Permission, MapConst_3_4497(0)))
           == MapConst_5_3570(true)
         && MapImp_3570(Set_Collector_4497(pSet), 
            MapEq_4497_3(Civl_partition_Permission, MapConst_3_4497(1)))
           == MapConst_5_3570(true));
    // <<< injected gate
    assert true
       ==> sps
         == Set_4497((lambda x: Permission :: 
            x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
    // injected gate >>>
    call Civl_returnedPAs_read_f := atomic_main_f(tid, sps);
    assert Civl_returnedPAs_read_f == MapConst_3_9258(0);
    Civl_eval := mem == Civl_global_old_mem
       && r1 == Civl_global_old_r1
       && r2 == Civl_global_old_r2
       && pSet == Civl_global_old_pSet
       && (done_first <==> Civl_global_old_done_first)
       && (done_second <==> Civl_global_old_done_second);
    goto anon0_3, Civl_NoninterferenceChecker, Civl_RefinementChecker;

  anon0_3:
    Civl_pc, Civl_ok := mem == Civl_global_old_mem
         && r1 == Civl_global_old_r1
         && r2 == Civl_global_old_r2
         && pSet == Civl_global_old_pSet
         && (done_first <==> Civl_global_old_done_first)
         && (done_second <==> Civl_global_old_done_second)
       ==> Civl_pc, Civl_eval || Civl_ok;
    call Civl_ParallelCall_Yield_1();
    assume Civl_pc || true;
    Civl_global_old_mem, Civl_global_old_r1, Civl_global_old_r2, Civl_global_old_pSet, Civl_global_old_done_first, Civl_global_old_done_second := mem, r1, r2, pSet, done_first, done_second;
    Civl_linear_Permission_available := MapOr_4497(Set_Collector_4497(pSet), MapConst_5_3570(false));
    call atomic_check_first();
    Civl_eval := mem == Civl_global_old_mem
       && r1 == Civl_global_old_r1
       && r2 == Civl_global_old_r2
       && pSet == Civl_global_old_pSet
       && (done_first <==> Civl_global_old_done_first)
       && (done_second <==> Civl_global_old_done_second);
    goto anon0_2, Civl_NoninterferenceChecker, Civl_RefinementChecker;

  anon0_2:
    Civl_pc, Civl_ok := mem == Civl_global_old_mem
         && r1 == Civl_global_old_r1
         && r2 == Civl_global_old_r2
         && pSet == Civl_global_old_pSet
         && (done_first <==> Civl_global_old_done_first)
         && (done_second <==> Civl_global_old_done_second)
       ==> Civl_pc, Civl_eval || Civl_ok;
    call Civl_ParallelCall_Yield_1();
    assume Civl_pc || true;
    Civl_global_old_mem, Civl_global_old_r1, Civl_global_old_r2, Civl_global_old_pSet, Civl_global_old_done_first, Civl_global_old_done_second := mem, r1, r2, pSet, done_first, done_second;
    Civl_linear_Permission_available := MapOr_4497(Set_Collector_4497(pSet), MapConst_5_3570(false));
    // <<< injected gate
    assert Set_IsSubset_3570(Set_4497((lambda x: Permission :: 
          x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n)), 
      pSet);
    // injected gate >>>
    call sps := atomic_get_permissions(tid);
    Civl_eval := mem == Civl_global_old_mem
       && r1 == Civl_global_old_r1
       && r2 == Civl_global_old_r2
       && pSet == Civl_global_old_pSet
       && (done_first <==> Civl_global_old_done_first)
       && (done_second <==> Civl_global_old_done_second);
    goto anon0_1, Civl_NoninterferenceChecker, Civl_RefinementChecker;

  anon0_1:
    Civl_pc, Civl_ok := mem == Civl_global_old_mem
         && r1 == Civl_global_old_r1
         && r2 == Civl_global_old_r2
         && pSet == Civl_global_old_pSet
         && (done_first <==> Civl_global_old_done_first)
         && (done_second <==> Civl_global_old_done_second)
       ==> Civl_pc, Civl_eval || Civl_ok;
    call Civl_ParallelCall_Yield_1();
    assume Civl_pc || true;
    Civl_global_old_mem, Civl_global_old_r1, Civl_global_old_r2, Civl_global_old_pSet, Civl_global_old_done_first, Civl_global_old_done_second := mem, r1, r2, pSet, done_first, done_second;
    Civl_linear_Permission_available := MapOr_4497(Set_Collector_4497(pSet), 
      MapOr_4497(Set_Collector_4497(sps), MapConst_5_3570(false)));
    assume (exists Civl_partition_Permission: [Permission]int :: 
      MapImp_3570(Set_Collector_4497(sps), 
            MapEq_4497_3(Civl_partition_Permission, MapConst_3_4497(0)))
           == MapConst_5_3570(true)
         && MapImp_3570(Set_Collector_4497(pSet), 
            MapEq_4497_3(Civl_partition_Permission, MapConst_3_4497(1)))
           == MapConst_5_3570(true));
    // <<< injected gate
    assert true
       ==> sps
         == Set_4497((lambda x: Permission :: 
            x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
    // injected gate >>>
    call Civl_returnedPAs_read_f := atomic_main_s(tid, sps);
    assert Civl_returnedPAs_read_f == MapConst_3_9258(0);
    Civl_eval := mem == Civl_global_old_mem
       && r1 == Civl_global_old_r1
       && r2 == Civl_global_old_r2
       && pSet == Civl_global_old_pSet
       && (done_first <==> Civl_global_old_done_first)
       && (done_second <==> Civl_global_old_done_second);
    goto anon0_0, Civl_NoninterferenceChecker, Civl_RefinementChecker;

  anon0_0:
    Civl_pc, Civl_ok := mem == Civl_global_old_mem
         && r1 == Civl_global_old_r1
         && r2 == Civl_global_old_r2
         && pSet == Civl_global_old_pSet
         && (done_first <==> Civl_global_old_done_first)
         && (done_second <==> Civl_global_old_done_second)
       ==> Civl_pc, Civl_eval || Civl_ok;
    call Civl_ParallelCall_Yield_1();
    assume Civl_pc || true;
    Civl_global_old_mem, Civl_global_old_r1, Civl_global_old_r2, Civl_global_old_pSet, Civl_global_old_done_first, Civl_global_old_done_second := mem, r1, r2, pSet, done_first, done_second;
    Civl_linear_Permission_available := MapOr_4497(Set_Collector_4497(pSet), MapConst_5_3570(false));
    call atomic_check_second();
    goto Civl_ReturnChecker, Civl_UnifiedReturn, Civl_NoninterferenceChecker;

  Civl_NoninterferenceChecker:
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Permission_available, Civl_global_old_mem, Civl_global_old_r1, Civl_global_old_r2, Civl_global_old_pSet, Civl_global_old_done_first, Civl_global_old_done_second);
    assume false;
    return;

  Civl_RefinementChecker:
    assert Civl_pc
       || 
      (
        mem == Civl_global_old_mem
         && r1 == Civl_global_old_r1
         && r2 == Civl_global_old_r2
         && pSet == Civl_global_old_pSet
         && (done_first <==> Civl_global_old_done_first)
         && (done_second <==> Civl_global_old_done_second))
       || Civl_eval;
    assert Civl_pc
       ==> mem == Civl_global_old_mem
         && r1 == Civl_global_old_r1
         && r2 == Civl_global_old_r2
         && pSet == Civl_global_old_pSet
         && (done_first <==> Civl_global_old_done_first)
         && (done_second <==> Civl_global_old_done_second);
    assume false;
    return;

  Civl_UnchangedChecker:
    assert mem == Civl_global_old_mem
       && r1 == Civl_global_old_r1
       && r2 == Civl_global_old_r2
       && pSet == Civl_global_old_pSet
       && (done_first <==> Civl_global_old_done_first)
       && (done_second <==> Civl_global_old_done_second);
    assert Civl_pc ==> true;
    assume false;
    return;

  Civl_ReturnChecker:
    Civl_eval := mem == Civl_global_old_mem
       && r1 == Civl_global_old_r1
       && r2 == Civl_global_old_r2
       && pSet == Civl_global_old_pSet
       && (done_first <==> Civl_global_old_done_first)
       && (done_second <==> Civl_global_old_done_second);
    assert Civl_pc
       || 
      (
        mem == Civl_global_old_mem
         && r1 == Civl_global_old_r1
         && r2 == Civl_global_old_r2
         && pSet == Civl_global_old_pSet
         && (done_first <==> Civl_global_old_done_first)
         && (done_second <==> Civl_global_old_done_second))
       || Civl_eval;
    assert Civl_pc
       ==> mem == Civl_global_old_mem
         && r1 == Civl_global_old_r1
         && r2 == Civl_global_old_r2
         && pSet == Civl_global_old_pSet
         && (done_first <==> Civl_global_old_done_first)
         && (done_second <==> Civl_global_old_done_second);
    Civl_pc, Civl_ok := mem == Civl_global_old_mem
         && r1 == Civl_global_old_r1
         && r2 == Civl_global_old_r2
         && pSet == Civl_global_old_pSet
         && (done_first <==> Civl_global_old_done_first)
         && (done_second <==> Civl_global_old_done_second)
       ==> Civl_pc, Civl_eval || Civl_ok;
    assert Civl_ok;
    assume false;
    return;

  Civl_UnifiedReturn:
    return;
}



procedure {:inline 1} Civl_NoninterferenceChecker_yield_Yield(Civl_linear_Permission_in: [Permission]bool, 
    Civl_snapshot_mem: [int]StampedValue, 
    Civl_snapshot_r1: [Tid][int]StampedValue, 
    Civl_snapshot_r2: [Tid][int]StampedValue, 
    Civl_snapshot_pSet: Set_4497, 
    Civl_snapshot_done_first: bool, 
    Civl_snapshot_done_second: bool);



implementation Civl_NoninterferenceChecker_yield_Yield(Civl_linear_Permission_in: [Permission]bool, 
    Civl_snapshot_mem: [int]StampedValue, 
    Civl_snapshot_r1: [Tid][int]StampedValue, 
    Civl_snapshot_r2: [Tid][int]StampedValue, 
    Civl_snapshot_pSet: Set_4497, 
    Civl_snapshot_done_first: bool, 
    Civl_snapshot_done_second: bool)
{

  enter:
    goto exit, L;

  exit:
    return;

  L:
    assume true;
    assert true;
    assume false;
    return;
}



procedure Civl_ParallelCall_Yield_1();
  requires true;
  modifies mem, r1, r2, pSet, done_first, done_second;
  ensures true;



procedure Civl_PendingAsyncNoninterferenceChecker_read_f_1(perm: One_4830);
  requires 1 <= perm->val->mem_index && perm->val->mem_index <= n;
  modifies mem, r1, r2, pSet, done_first, done_second;



implementation Civl_PendingAsyncNoninterferenceChecker_read_f_1(perm: One_4830)
{
  var Civl_global_old_mem: [int]StampedValue;
  var Civl_global_old_r1: [Tid][int]StampedValue;
  var Civl_global_old_r2: [Tid][int]StampedValue;
  var Civl_global_old_pSet: Set_4497;
  var Civl_global_old_done_first: bool;
  var Civl_global_old_done_second: bool;
  var Civl_linear_Permission_available: [Permission]bool;

  init:
    Civl_global_old_mem, Civl_global_old_r1, Civl_global_old_r2, Civl_global_old_pSet, Civl_global_old_done_first, Civl_global_old_done_second := mem, r1, r2, pSet, done_first, done_second;
    Civl_linear_Permission_available := MapOr_4497(Set_Collector_4497(pSet), 
      MapOr_4497(One_Collector_4830(perm), MapConst_5_3570(false)));
    call read_f(perm);
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Permission_available, Civl_global_old_mem, Civl_global_old_r1, Civl_global_old_r2, Civl_global_old_pSet, Civl_global_old_done_first, Civl_global_old_done_second);
    return;
}



procedure Civl_PendingAsyncNoninterferenceChecker_atomic_main_s_1(tid: Tid, sps: Set_4497) returns (Civl_PAs_read_f: [read_f]int);
  requires true
     ==> sps
       == Set_4497((lambda x: Permission :: 
          x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
  modifies mem, r1, r2, pSet, done_first, done_second;



implementation Civl_PendingAsyncNoninterferenceChecker_atomic_main_s_1(tid: Tid, sps: Set_4497) returns (Civl_PAs_read_f: [read_f]int)
{
  var Civl_global_old_mem: [int]StampedValue;
  var Civl_global_old_r1: [Tid][int]StampedValue;
  var Civl_global_old_r2: [Tid][int]StampedValue;
  var Civl_global_old_pSet: Set_4497;
  var Civl_global_old_done_first: bool;
  var Civl_global_old_done_second: bool;
  var Civl_linear_Permission_available: [Permission]bool;

  init:
    Civl_global_old_mem, Civl_global_old_r1, Civl_global_old_r2, Civl_global_old_pSet, Civl_global_old_done_first, Civl_global_old_done_second := mem, r1, r2, pSet, done_first, done_second;
    Civl_linear_Permission_available := MapOr_4497(Set_Collector_4497(pSet), 
      MapOr_4497(Set_Collector_4497(sps), MapConst_5_3570(false)));
    call Civl_PAs_read_f := atomic_main_s(tid, sps);
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Permission_available, Civl_global_old_mem, Civl_global_old_r1, Civl_global_old_r2, Civl_global_old_pSet, Civl_global_old_done_first, Civl_global_old_done_second);
    return;
}



procedure Civl_PendingAsyncNoninterferenceChecker_atomic_main_f_1(tid: Tid, sps: Set_4497) returns (Civl_PAs_read_f: [read_f]int);
  requires true
     ==> sps
       == Set_4497((lambda x: Permission :: 
          x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
  modifies mem, r1, r2, pSet, done_first, done_second;



implementation Civl_PendingAsyncNoninterferenceChecker_atomic_main_f_1(tid: Tid, sps: Set_4497) returns (Civl_PAs_read_f: [read_f]int)
{
  var Civl_global_old_mem: [int]StampedValue;
  var Civl_global_old_r1: [Tid][int]StampedValue;
  var Civl_global_old_r2: [Tid][int]StampedValue;
  var Civl_global_old_pSet: Set_4497;
  var Civl_global_old_done_first: bool;
  var Civl_global_old_done_second: bool;
  var Civl_linear_Permission_available: [Permission]bool;

  init:
    Civl_global_old_mem, Civl_global_old_r1, Civl_global_old_r2, Civl_global_old_pSet, Civl_global_old_done_first, Civl_global_old_done_second := mem, r1, r2, pSet, done_first, done_second;
    Civl_linear_Permission_available := MapOr_4497(Set_Collector_4497(pSet), 
      MapOr_4497(Set_Collector_4497(sps), MapConst_5_3570(false)));
    call Civl_PAs_read_f := atomic_main_f(tid, sps);
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Permission_available, Civl_global_old_mem, Civl_global_old_r1, Civl_global_old_r2, Civl_global_old_pSet, Civl_global_old_done_first, Civl_global_old_done_second);
    return;
}



procedure {:inline 1} Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Permission_in: [Permission]bool, 
    Civl_global_old_mem: [int]StampedValue, 
    Civl_global_old_r1: [Tid][int]StampedValue, 
    Civl_global_old_r2: [Tid][int]StampedValue, 
    Civl_global_old_pSet: Set_4497, 
    Civl_global_old_done_first: bool, 
    Civl_global_old_done_second: bool);



implementation Civl_Wrapper_NoninterferenceChecker_1(Civl_Civl_linear_Permission_in: [Permission]bool, 
    Civl_Civl_global_old_mem: [int]StampedValue, 
    Civl_Civl_global_old_r1: [Tid][int]StampedValue, 
    Civl_Civl_global_old_r2: [Tid][int]StampedValue, 
    Civl_Civl_global_old_pSet: Set_4497, 
    Civl_Civl_global_old_done_first: bool, 
    Civl_Civl_global_old_done_second: bool)
{

  enter:
    goto L_0;

  L_0:
    call Civl_NoninterferenceChecker_yield_Yield(Civl_Civl_linear_Permission_in, Civl_Civl_global_old_mem, Civl_Civl_global_old_r1, Civl_Civl_global_old_r2, Civl_Civl_global_old_pSet, Civl_Civl_global_old_done_first, Civl_Civl_global_old_done_second);
    return;
}



implementation Civl_LinearityChecker_atomic_main_s(tid: Tid, sps: Set_4497) returns (Civl_PAs_read_f: [read_f]int)
{
  var Civl_pa1_read_f: read_f;
  var Civl_pa2_read_f: read_f;

  init:
    call Civl_PAs_read_f := atomic_main_s(tid, sps);
    goto Permission_out_of_thin_air_read_f, Permission_duplication_read_f, Permission_duplication_read_f_read_f;

  Permission_out_of_thin_air_read_f:
    assume Civl_pa1_read_f is read_f && Civl_PAs_read_f[Civl_pa1_read_f] >= 1;
    assert MapImp_3570(MapOr_4497(One_Collector_4830(Civl_pa1_read_f->perm), MapConst_5_3570(false)), 
        old(MapOr_4497(Set_Collector_4497(sps), MapConst_5_3570(false))))
       == MapConst_5_3570(true);
    return;

  Permission_duplication_read_f:
    assume Civl_pa1_read_f is read_f && Civl_PAs_read_f[Civl_pa1_read_f] >= 1;
    assert MapAnd_4497(MapConst_5_3570(false), 
        MapOr_4497(One_Collector_4830(Civl_pa1_read_f->perm), MapConst_5_3570(false)))
       == MapConst_5_3570(false);
    return;

  Permission_duplication_read_f_read_f:
    assume Civl_pa1_read_f != Civl_pa2_read_f
       && 
      Civl_pa1_read_f is read_f
       && Civl_pa2_read_f is read_f
       && 
      Civl_PAs_read_f[Civl_pa1_read_f] >= 1
       && Civl_PAs_read_f[Civl_pa2_read_f] >= 1;
    assert MapAnd_4497(MapOr_4497(One_Collector_4830(Civl_pa1_read_f->perm), MapConst_5_3570(false)), 
        MapOr_4497(One_Collector_4830(Civl_pa2_read_f->perm), MapConst_5_3570(false)))
       == MapConst_5_3570(false);
    return;
}



procedure Civl_LinearityChecker_atomic_main_s(tid: Tid, sps: Set_4497) returns (Civl_PAs_read_f: [read_f]int);
  requires true
     ==> sps
       == Set_4497((lambda x: Permission :: 
          x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
  requires true;



implementation Civl_LinearityChecker_atomic_main_f(tid: Tid, sps: Set_4497) returns (Civl_PAs_read_f: [read_f]int)
{
  var Civl_pa1_read_f: read_f;
  var Civl_pa2_read_f: read_f;

  init:
    call Civl_PAs_read_f := atomic_main_f(tid, sps);
    goto Permission_out_of_thin_air_read_f, Permission_duplication_read_f, Permission_duplication_read_f_read_f;

  Permission_out_of_thin_air_read_f:
    assume Civl_pa1_read_f is read_f && Civl_PAs_read_f[Civl_pa1_read_f] >= 1;
    assert MapImp_3570(MapOr_4497(One_Collector_4830(Civl_pa1_read_f->perm), MapConst_5_3570(false)), 
        old(MapOr_4497(Set_Collector_4497(sps), MapConst_5_3570(false))))
       == MapConst_5_3570(true);
    return;

  Permission_duplication_read_f:
    assume Civl_pa1_read_f is read_f && Civl_PAs_read_f[Civl_pa1_read_f] >= 1;
    assert MapAnd_4497(MapConst_5_3570(false), 
        MapOr_4497(One_Collector_4830(Civl_pa1_read_f->perm), MapConst_5_3570(false)))
       == MapConst_5_3570(false);
    return;

  Permission_duplication_read_f_read_f:
    assume Civl_pa1_read_f != Civl_pa2_read_f
       && 
      Civl_pa1_read_f is read_f
       && Civl_pa2_read_f is read_f
       && 
      Civl_PAs_read_f[Civl_pa1_read_f] >= 1
       && Civl_PAs_read_f[Civl_pa2_read_f] >= 1;
    assert MapAnd_4497(MapOr_4497(One_Collector_4830(Civl_pa1_read_f->perm), MapConst_5_3570(false)), 
        MapOr_4497(One_Collector_4830(Civl_pa2_read_f->perm), MapConst_5_3570(false)))
       == MapConst_5_3570(false);
    return;
}



procedure Civl_LinearityChecker_atomic_main_f(tid: Tid, sps: Set_4497) returns (Civl_PAs_read_f: [read_f]int);
  requires true
     ==> sps
       == Set_4497((lambda x: Permission :: 
          x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
  requires true;



procedure Civl_PartitionChecker_atomic_main_f(tid: Tid, sps: Set_4497) returns (Civl_PAs_read_f: [read_f]int);



implementation Civl_PartitionChecker_atomic_main_f(tid: Tid, sps: Set_4497) returns (Civl_PAs_read_f: [read_f]int)
{
  var Civl_local_Civl_PAs_read_f: read_f;

  Civl_PartitionChecker_atomic_main_f:
    call Civl_PAs_read_f := atomic_main_f(tid, sps);
    assert Civl_PAs_read_f != MapConst_3_9258(0) ==> true;
    goto label_Civl_PAs_read_f;

  label_Civl_PAs_read_f:
    assume Civl_PAs_read_f[Civl_local_Civl_PAs_read_f] >= 1;
    assert 1 <= Civl_local_Civl_PAs_read_f->perm->val->mem_index
       && Civl_local_Civl_PAs_read_f->perm->val->mem_index <= n;
    return;
}



procedure Civl_PartitionChecker_read_f(perm: One_4830);
  modifies r1, pSet, done_first;



implementation Civl_PartitionChecker_read_f(perm: One_4830)
{

  Civl_PartitionChecker_read_f:
    call read_f(perm);
    assert false ==> true;
    return;
}



procedure Civl_ISR_base_atomic_main_f(tid: Tid, sps: Set_4497) returns (Civl_PAs_read_f: [read_f]int);
  requires (forall j: int :: 
    0 <= j && j <= n
       ==> (forall r1: [Tid][int]StampedValue :: 
        (forall i: int :: 
            1 <= i && i <= j ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i])
           ==> 
          true
           ==> Set_IsSubset_3570(Set_4497((lambda {:pool "D"} x: Permission :: 
                x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j)), 
            sps)));
  requires sps == WholeTidPermission(tid);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3570(Set_Collector_4497(sps), 
          MapEq_4497_3(Civl_partition_Permission, MapConst_3_4497(0)))
         == MapConst_5_3570(true)
       && MapImp_3570(Set_Collector_4497(pSet), 
          MapEq_4497_3(Civl_partition_Permission, MapConst_3_4497(1)))
         == MapConst_5_3570(true));
  modifies r1, pSet, done_first;



implementation Civl_ISR_base_atomic_main_f(tid: Tid, sps: Set_4497) returns (Civl_PAs_read_f: [read_f]int)
{

  ISR_base_atomic_main_f:
    assert true
       ==> sps
         == Set_4497((lambda x: Permission :: 
            x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
    call Civl_PAs_read_f := atomic_main_f(tid, sps);
    assert (exists {:pool "A"} Civl_j#0: int :: 
        0 <= Civl_j#0
           && Civl_j#0 <= n
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0 ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i])
           && true
           && Civl_j#0 < n
           && true
           && pSet
             == Set_Union_4497(old(pSet), 
              Set_4497((lambda {:pool "D"} x: Permission :: 
                  x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
           && Civl_PAs_read_f
             == MapAdd_9247(MapConst_3_9258(0), 
              MapIte_9265_3((lambda {:pool "C"} pa: read_f :: 
                  Civl_j#0 + 1 <= pa->perm->val->mem_index
                     && pa->perm->val->mem_index <= n
                     && pa->perm->val->t_id == tid), 
                MapConst_3_9258(1), 
                MapConst_3_9258(0)))
           && (done_first <==> old(done_first)))
       || (exists {:pool "A"} Civl_j#0: int :: 
        0 <= Civl_j#0
           && Civl_j#0 <= n
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0 ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i])
           && true
           && n <= Civl_j#0
           && Civl_PAs_read_f == MapConst_3_9258(0)
           && pSet
             == Set_Union_4497(old(pSet), 
              Set_4497((lambda {:pool "D"} x: Permission :: 
                  x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
           && (done_first <==> true));
    return;
}



procedure Civl_ISR_conclusion_atomic_main_f(tid: Tid, sps: Set_4497) returns (Civl_PAs_read_f: [read_f]int);
  requires true
     ==> (forall r1: [Tid][int]StampedValue :: 
      (forall i: int :: 
          1 <= i && i <= n ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i])
         ==> Set_IsSubset_3570(Set_4497((lambda x: Permission :: 
              x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n)), 
          sps));
  requires true
     ==> sps
       == Set_4497((lambda x: Permission :: 
          x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3570(Set_Collector_4497(sps), 
          MapEq_4497_3(Civl_partition_Permission, MapConst_3_4497(0)))
         == MapConst_5_3570(true)
       && MapImp_3570(Set_Collector_4497(pSet), 
          MapEq_4497_3(Civl_partition_Permission, MapConst_3_4497(1)))
         == MapConst_5_3570(true));
  modifies r1, pSet, done_first;



implementation Civl_ISR_conclusion_atomic_main_f(tid: Tid, sps: Set_4497) returns (Civl_PAs_read_f: [read_f]int)
{

  ISR_conclusion_atomic_main_f:
    assert (forall j: int :: 
      0 <= j && j <= n
         ==> (forall r1: [Tid][int]StampedValue :: 
          (forall i: int :: 
              1 <= i && i <= j ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i])
             ==> 
            true
             ==> Set_IsSubset_3570(Set_4497((lambda {:pool "D"} x: Permission :: 
                  x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j)), 
              sps)));
    assert sps == WholeTidPermission(tid);
    call Civl_PAs_read_f := Inv_f(tid, sps);
    assume Civl_PAs_read_f == MapConst_3_9258(0);
    assert true
       && (forall i: int :: 
        1 <= i && i <= n ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i])
       && pSet
         == Set_Union_4497(old(pSet), 
          Set_4497((lambda x: Permission :: 
              x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n)))
       && (done_first <==> true)
       && mem == old(mem)
       && r2 == old(r2)
       && (done_second <==> old(done_second));
    return;
}



procedure Civl_ISR_step_Inv_f_read_f(tid: Tid, sps: Set_4497)
   returns (Civl_PAs_read_f: [read_f]int, Civl_choice: Choice_Inv_f);
  requires (forall j: int :: 
    0 <= j && j <= n
       ==> (forall r1: [Tid][int]StampedValue :: 
        (forall i: int :: 
            1 <= i && i <= j ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i])
           ==> 
          true
           ==> Set_IsSubset_3570(Set_4497((lambda {:pool "D"} x: Permission :: 
                x->t_id == tid && 1 <= x->mem_index && x->mem_index <= j)), 
            sps)));
  requires sps == WholeTidPermission(tid);
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3570(Set_Collector_4497(sps), 
          MapEq_4497_3(Civl_partition_Permission, MapConst_3_4497(0)))
         == MapConst_5_3570(true)
       && MapImp_3570(Set_Collector_4497(pSet), 
          MapEq_4497_3(Civl_partition_Permission, MapConst_3_4497(1)))
         == MapConst_5_3570(true));
  modifies r1, pSet, done_first;



implementation Civl_ISR_step_Inv_f_read_f(tid: Tid, sps: Set_4497)
   returns (Civl_PAs_read_f: [read_f]int, Civl_choice: Choice_Inv_f)
{

  ISR_step_Inv_f_read_f:
    call Civl_PAs_read_f, Civl_choice := Inv_f_With_Choice(tid, sps);
    assume Civl_choice is Choice_Inv_f_read_f;
    assume Civl_PAs_read_f[Civl_choice->read_f] > 0;
    Civl_PAs_read_f[Civl_choice->read_f] := Civl_PAs_read_f[Civl_choice->read_f] - 1;
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
             == Set_Union_4497(old(pSet), 
              Set_4497((lambda {:pool "D"} x: Permission :: 
                  x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
           && Civl_PAs_read_f
             == MapAdd_9247(MapConst_3_9258(0), 
              MapIte_9265_3((lambda {:pool "C"} pa: read_f :: 
                  Civl_j#0 + 1 <= pa->perm->val->mem_index
                     && pa->perm->val->mem_index <= n
                     && pa->perm->val->t_id == tid), 
                MapConst_3_9258(1), 
                MapConst_3_9258(0)))
           && (done_first <==> old(done_first)))
       || (exists {:pool "A"} Civl_j#0: int :: 
        0 <= Civl_j#0
           && Civl_j#0 <= n
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0 ==> r1[tid][i]->ts < mem[i]->ts || r1[tid][i] == mem[i])
           && true
           && n <= Civl_j#0
           && Civl_PAs_read_f == MapConst_3_9258(0)
           && pSet
             == Set_Union_4497(old(pSet), 
              Set_4497((lambda {:pool "D"} x: Permission :: 
                  x->t_id == tid && 1 <= x->mem_index && x->mem_index <= Civl_j#0)))
           && (done_first <==> true));
    return;
}



procedure Civl_ISR_SideCondition_atomic_main_f(tid: Tid, sps: Set_4497) returns (Civl_PAs_read_f: [read_f]int);
  requires true
     ==> sps
       == Set_4497((lambda x: Permission :: 
          x->t_id == tid && 1 <= x->mem_index && x->mem_index <= n));
  requires true;



implementation Civl_ISR_SideCondition_atomic_main_f(tid: Tid, sps: Set_4497) returns (Civl_PAs_read_f: [read_f]int)
{

  init:
    call Civl_PAs_read_f := atomic_main_f(tid, sps);
    goto Permission_only_put_perm_atomic_main_f;

  Permission_only_put_perm_atomic_main_f:
    assume true;
    assert MapImp_3570(old(MapConst_5_3570(false)), MapConst_5_3570(false))
       == MapConst_5_3570(true);
    return;
}



procedure Civl_ISR_ExitProperty_AllPendingAsyncsInElim_read_f(perm: One_4830);
  modifies r1, pSet, done_first;



implementation Civl_ISR_ExitProperty_AllPendingAsyncsInElim_read_f(perm: One_4830)
{

  ISR_ExitProperty_AllPendingAsyncsInElim_read_f:
    assume !Set_IsSubset_3570(WholeTidPermission(perm->val->t_id), Set_Add_3567(pSet, perm->val));
    call read_f(perm);
    assert true;
    return;
}



procedure Civl_ISR_ExitProperty_AllPendingAsyncsNotInElim_read_f(perm: One_4830);
  modifies r1, pSet, done_first;



implementation Civl_ISR_ExitProperty_AllPendingAsyncsNotInElim_read_f(perm: One_4830)
{

  ISR_ExitProperty_AllPendingAsyncsNotInElim_read_f:
    assume Set_IsSubset_3570(WholeTidPermission(perm->val->t_id), Set_Add_3567(pSet, perm->val));
    call read_f(perm);
    assert true;
    return;
}



procedure Civl_ISR_SideCondition_read_f(perm: One_4830);
  requires 1 <= perm->val->mem_index && perm->val->mem_index <= n;
  requires (exists Civl_partition_Permission: [Permission]int :: 
    MapImp_3570(One_Collector_4830(perm), 
          MapEq_4497_3(Civl_partition_Permission, MapConst_3_4497(0)))
         == MapConst_5_3570(true)
       && MapImp_3570(Set_Collector_4497(pSet), 
          MapEq_4497_3(Civl_partition_Permission, MapConst_3_4497(1)))
         == MapConst_5_3570(true));
  modifies r1, pSet, done_first;



implementation Civl_ISR_SideCondition_read_f(perm: One_4830)
{

  init:
    call read_f(perm);
    goto Permission_only_put_perm_read_f;

  Permission_only_put_perm_read_f:
    assume true;
    assert MapImp_3570(old(MapOr_4497(Set_Collector_4497(pSet), MapConst_5_3570(false))), 
        MapOr_4497(Set_Collector_4497(pSet), MapConst_5_3570(false)))
       == MapConst_5_3570(true);
    return;
}



procedure Civl_ISR_InconsistencyChecker_atomic_main_f_read_f_read_f();
  modifies r1, pSet, done_first;



implementation Civl_ISR_InconsistencyChecker_atomic_main_f_read_f_read_f()
{
  var Civl_E1_read_f: read_f;
  var Civl_E2_read_f: read_f;
  var Civl_tempg_mem: [int]StampedValue;
  var Civl_tempg_r1: [Tid][int]StampedValue;
  var Civl_tempg_r2: [Tid][int]StampedValue;
  var Civl_tempg_pSet: Set_4497;
  var Civl_tempg_done_first: bool;
  var Civl_tempg_done_second: bool;
  var Civl_templ_tid: Tid;
  var Civl_templ_sps: Set_4497;

  ISR_InconsistencyChecker_atomic_main_f_read_f_read_f:
    assume (true
         ==> Civl_templ_sps
           == Set_4497((lambda x: Permission :: 
              x->t_id == Civl_templ_tid && 1 <= x->mem_index && x->mem_index <= n)))
       && true;
    assume MapAnd_4497(MapOr_4497(Set_Collector_4497(pSet), MapConst_5_3570(false)), 
          MapOr_4497(One_Collector_4830(Civl_E1_read_f->perm), MapConst_5_3570(false)))
         == MapConst_5_3570(false)
       && MapAnd_4497(MapOr_4497(Set_Collector_4497(pSet), MapConst_5_3570(false)), 
          MapOr_4497(One_Collector_4830(Civl_E2_read_f->perm), MapConst_5_3570(false)))
         == MapConst_5_3570(false)
       && MapAnd_4497(MapOr_4497(One_Collector_4830(Civl_E1_read_f->perm), MapConst_5_3570(false)), 
          MapOr_4497(One_Collector_4830(Civl_E2_read_f->perm), MapConst_5_3570(false)))
         == MapConst_5_3570(false);
    assume MapImp_3570(MapOr_4497(One_Collector_4830(Civl_E1_read_f->perm), MapConst_5_3570(false)), 
          MapOr_4497(Set_Collector_4497(Civl_templ_sps), MapConst_5_3570(false)))
         == MapConst_5_3570(true)
       && MapImp_3570(MapOr_4497(One_Collector_4830(Civl_E2_read_f->perm), MapConst_5_3570(false)), 
          MapOr_4497(Set_Collector_4497(Civl_templ_sps), MapConst_5_3570(false)))
         == MapConst_5_3570(true);
    assert !(
      1 <= Civl_E1_read_f->perm->val->mem_index
       && Civl_E1_read_f->perm->val->mem_index <= n
       && 
      Set_IsSubset_3570(WholeTidPermission(Civl_E2_read_f->perm->val->t_id), 
        Set_Add_3567(pSet, Civl_E2_read_f->perm->val))
       && 
      1 <= Civl_E2_read_f->perm->val->mem_index
       && Civl_E2_read_f->perm->val->mem_index <= n);
    return;
}


