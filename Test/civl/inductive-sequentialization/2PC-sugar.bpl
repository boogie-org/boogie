// Boogie program verifier version 3.2.3.0, Copyright (c) 2003-2014, Microsoft.
// Command Line Options: 2PC.bpl /trace /trustMoverTypes /civlDesugaredFile:2PC-sugar.bpl

type Pid = int;

datatype vote {
  YES(),
  NO()
}

datatype decision {
  COMMIT(),
  ABORT(),
  NONE()
}

const n: int;

function {:inline} pid(pid: int) : bool
{
  1 <= pid && pid <= n
}

function {:inline} pidLe(pid: int, k: int) : bool
{
  1 <= pid && pid <= k
}

function {:inline} pidGt(pid: int, k: int) : bool
{
  k < pid && pid <= n
}

var RequestChannel: [int]int;

var DecisionChannel: [int][decision]int;

var VoteChannel: [vote]int;

var votes: [int]vote;

var decisions: [int]decision;

function {:inline} Init(pids: [int]bool, 
    RequestChannel: [int]int, 
    VoteChannel: [vote]int, 
    DecisionChannel: [int][decision]int, 
    decisions: [int]decision)
   : bool
{
  pids == MapConst_5_150(true)
     && RequestChannel == (lambda i: int :: 0)
     && VoteChannel == (lambda v: vote :: 0)
     && DecisionChannel == (lambda i: int :: (lambda d: decision :: 0))
     && decisions == (lambda i: int :: NONE())
}

datatype PARTICIPANT1 {
  PARTICIPANT1(pid: One_43)
}

datatype PARTICIPANT2 {
  PARTICIPANT2(pid: One_43)
}

datatype COORDINATOR1 {
  COORDINATOR1(pid: One_43)
}

datatype COORDINATOR2 {
  COORDINATOR2(pid: One_43)
}

const Identity: [int]int;

function {:inline} AtLeast(x: int) : [int]bool
{
  MapLe_2942(MapConst_2959_2942(x), Identity)
}

function {:inline} Range(from: int, n: int) : [int]bool
{
  MapDiff_2962(AtLeast(from), AtLeast(from + n))
}

type {:builtin "Seq"} Seq _;

pure procedure Assume(b: bool);
  ensures b;



function {:builtin "MapConst"} MapConst_5_150(bool) : [int]bool;

datatype Set_230 {
  Set_230(val: [int]bool)
}

datatype One_43 {
  One_43(val: int)
}

pure procedure Set_Get_335(path: Set_230, k: [int]bool) returns (l: Set_230);



procedure create_asyncs_4801(PAs: [PARTICIPANT2]bool);



procedure set_choice_4752(choice: PARTICIPANT2);



pure procedure One_Get_687(path: Set_230, k: int) returns (l: One_43);



procedure create_asyncs_4825(PAs: [PARTICIPANT1]bool);



procedure set_choice_4750(choice: PARTICIPANT1);



function {:builtin "MapConst"} MapConst_3_4754(int) : [COORDINATOR1]int;

pure procedure {:inline 1} Copy_9661(v: [int]int) returns (copy_v: [int]int);



implementation {:inline 1} Copy_9661(v: [int]int) returns (copy_v: [int]int)
{

  anon0:
    copy_v := v;
    return;
}



pure procedure {:inline 1} Copy_9822(v: [vote]int) returns (copy_v: [vote]int);



implementation {:inline 1} Copy_9822(v: [vote]int) returns (copy_v: [vote]int)
{

  anon0:
    copy_v := v;
    return;
}



pure procedure {:inline 1} Copy_9869(v: [int][decision]int) returns (copy_v: [int][decision]int);



implementation {:inline 1} Copy_9869(v: [int][decision]int) returns (copy_v: [int][decision]int)
{

  anon0:
    copy_v := v;
    return;
}



function {:builtin "MapConst"} MapConst_2959_2942(int) : [int]int;

function {:builtin "MapLe"} MapLe_2942([int]int, [int]int) : [int]bool;

function {:inline} MapDiff_2962(a: [int]bool, b: [int]bool) : [int]bool
{
  MapAnd_2962(a, MapNot_2962(b))
}

function {:builtin "MapNot"} MapNot_2962([int]bool) : [int]bool;

function {:builtin "MapAnd"} MapAnd_2962([int]bool, [int]bool) : [int]bool;

datatype Vec_5 {
  Vec_5(contents: [int]bool, len: int)
}

function Default_5() : bool;

function {:builtin "MapIte"} MapIte_2983_5([int]bool, [int]bool, [int]bool) : [int]bool;

datatype Vec_3 {
  Vec_3(contents: [int]int, len: int)
}

function Default_3() : int;

function {:builtin "MapIte"} MapIte_2983_3([int]bool, [int]int, [int]int) : [int]int;

function Choice_150(a: [int]bool) : int;

function {:builtin "MapConst"} MapConst_5_4754(bool) : [COORDINATOR1]bool;

function Choice_4754(a: [COORDINATOR1]bool) : COORDINATOR1;

axiom n > 0;

axiom (forall x: int :: Identity[x] == x);

axiom (forall x: Vec_3 :: 
  { x->len } { x->contents } 
  MapIte_2983_3(Range(0, x->len), MapConst_2959_2942(Default_3()), x->contents)
     == MapConst_2959_2942(Default_3()));

axiom (forall x: Vec_5 :: 
  { x->len } { x->contents } 
  MapIte_2983_5(Range(0, x->len), MapConst_5_150(Default_5()), x->contents)
     == MapConst_5_150(Default_5()));

axiom (forall x: Vec_3 :: { x->len } x->len >= 0);

axiom (forall x: Vec_5 :: { x->len } x->len >= 0);

axiom (forall a: [COORDINATOR1]bool :: 
  { Choice_4754(a) } 
  a == MapConst_5_4754(false) || a[Choice_4754(a)]);

axiom (forall a: [int]bool :: 
  { Choice_150(a) } 
  a == MapConst_5_150(false) || a[Choice_150(a)]);

function {:builtin "MapOr"} MapOr_230([int]bool, [int]bool) : [int]bool;

function {:builtin "MapImp"} MapImp_230([int]bool, [int]bool) : [int]bool;

function {:builtin "MapEq"} MapEq_230_3([int]int, [int]int) : [int]bool;

function {:builtin "MapAdd"} MapAdd_230([int]int, [int]int) : [int]int;

function {:inline} Set_Collector_230(a: Set_230) : [int]bool
{
  a->val
}

function {:inline} One_Collector_43(a: One_43) : [int]bool
{
  MapOne_43(a->val)
}

function {:inline} MapOne_43(t: int) : [int]bool
{
  MapConst_5_150(false)[t := true]
}

function {:inline} Collector_PARTICIPANT2_int(target: PARTICIPANT2) : [int]bool
{
  (if target is PARTICIPANT2
     then MapOr_230(One_Collector_43(target->pid), MapConst_5_150(false))
     else MapConst_5_150(false))
}

function {:inline} Collector_PARTICIPANT1_int(target: PARTICIPANT1) : [int]bool
{
  (if target is PARTICIPANT1
     then MapOr_230(One_Collector_43(target->pid), MapConst_5_150(false))
     else MapConst_5_150(false))
}

function {:inline} Collector_COORDINATOR1_int(target: COORDINATOR1) : [int]bool
{
  (if target is COORDINATOR1
     then MapOr_230(One_Collector_43(target->pid), MapConst_5_150(false))
     else MapConst_5_150(false))
}

function {:inline} Set_IsSubset_335(a: Set_230, b: Set_230) : bool
{
  IsSubset_335(a->val, b->val)
}

function {:inline} IsSubset_335(a: [int]bool, b: [int]bool) : bool
{
  MapImp_230(a, b) == MapConst_5_150(true)
}

function {:inline} Set_Difference_335(a: Set_230, b: Set_230) : Set_230
{
  Set_230(MapDiff_2962(a->val, b->val))
}

function {:inline} Set_Contains_43(a: Set_230, t: int) : bool
{
  a->val[t]
}

function {:inline} Set_Remove_687(a: Set_230, t: int) : Set_230
{
  Set_230(a->val[t := false])
}

function {:builtin "MapAdd"} MapAdd_14143([PARTICIPANT1]int, [PARTICIPANT1]int) : [PARTICIPANT1]int;

function {:builtin "MapConst"} MapConst_3_14154(int) : [PARTICIPANT1]int;

function {:builtin "MapIte"} MapIte_14161_3([PARTICIPANT1]bool, [PARTICIPANT1]int, [PARTICIPANT1]int) : [PARTICIPANT1]int;

function {:builtin "MapAdd"} MapAdd_14175([PARTICIPANT2]int, [PARTICIPANT2]int) : [PARTICIPANT2]int;

function {:builtin "MapConst"} MapConst_3_14186(int) : [PARTICIPANT2]int;

function {:builtin "MapIte"} MapIte_14193_3([PARTICIPANT2]bool, [PARTICIPANT2]int, [PARTICIPANT2]int) : [PARTICIPANT2]int;

function {:builtin "MapAdd"} MapAdd_14207([COORDINATOR1]int, [COORDINATOR1]int) : [COORDINATOR1]int;

function {:builtin "MapIte"} MapIte_14219_3([COORDINATOR1]bool, [COORDINATOR1]int, [COORDINATOR1]int) : [COORDINATOR1]int;

function {:builtin "MapAdd"} MapAdd_14233([COORDINATOR2]int, [COORDINATOR2]int) : [COORDINATOR2]int;

function {:builtin "MapConst"} MapConst_3_14244(int) : [COORDINATOR2]int;

function {:builtin "MapIte"} MapIte_14251_3([COORDINATOR2]bool, [COORDINATOR2]int, [COORDINATOR2]int) : [COORDINATOR2]int;

datatype Choice_INV4 {
  Choice_INV4_PARTICIPANT2(PARTICIPANT2: PARTICIPANT2)
}

datatype Choice_INV2 {
  Choice_INV2_COORDINATOR2(COORDINATOR2: COORDINATOR2),
  Choice_INV2_PARTICIPANT1(PARTICIPANT1: PARTICIPANT1),
  Choice_INV2_PARTICIPANT2(PARTICIPANT2: PARTICIPANT2)
}

function Trigger_MAIN5_dec(dec: decision) : bool;

function Trigger_INV4_k(k: int) : bool;

function Trigger_INV4_pids'(pids': Set_230) : bool;

function Trigger_INV4_participantPids(participantPids: Set_230) : bool;

function Trigger_INV2_pids'(pids': Set_230) : bool;

function Trigger_INV2_pid(pid: One_43) : bool;

function Trigger_INV2_participantPids(participantPids: Set_230) : bool;

function Trigger_INV2_k(k: int) : bool;

function Trigger_PARTICIPANT1_v(v: vote) : bool;

function Trigger_PARTICIPANT2_d(d: decision) : bool;

function Trigger_COORDINATOR2_dec(dec: decision) : bool;

function Trigger_MAIN4_dec(dec: decision) : bool;

function Trigger_MAIN4_pids'(pids': Set_230) : bool;

function Trigger_MAIN4_participantPids(participantPids: Set_230) : bool;

function Trigger_MAIN3_pids'(pids': Set_230) : bool;

function Trigger_MAIN3_pid(pid: One_43) : bool;

function Trigger_MAIN3_participantPids(participantPids: Set_230) : bool;

function Trigger_MAIN2_pids'(pids': Set_230) : bool;

function Trigger_MAIN2_pid(pid: One_43) : bool;

function Trigger_MAIN2_participantPids(participantPids: Set_230) : bool;

function Trigger_MAIN1_pids'(pids': Set_230) : bool;

function Trigger_MAIN1_pid(pid: One_43) : bool;

function Trigger_MAIN1_participantPids(participantPids: Set_230) : bool;

implementation MAIN5(pids: Set_230)
{
  var dec: decision;

  /*** structured program:
    assert Init(pids->val, RequestChannel, VoteChannel, DecisionChannel, decisions);
    havoc RequestChannel, VoteChannel, votes, decisions;
    if (*)
    {
        dec := COMMIT();
    }
    else
    {
        dec := ABORT();
    }

    assume dec == COMMIT() ==> (forall i: int :: pid(i) ==> votes[i] == YES());
    assume (forall i: int :: i == 0 || pid(i) ==> decisions[i] == dec);
  **** end structured program */

  anon0:
    havoc RequestChannel, VoteChannel, votes, decisions;
    goto anon4_Then, anon4_Else;

  anon4_Else:
    dec := ABORT();
    goto anon3;

  anon3:
    assume dec == COMMIT() ==> (forall i: int :: pid(i) ==> votes[i] == YES());
    assume (forall i: int :: i == 0 || pid(i) ==> decisions[i] == dec);
    return;

  anon4_Then:
    dec := COMMIT();
    goto anon3;
}



procedure {:inline 1} MAIN5(pids: Set_230);
  modifies RequestChannel, VoteChannel, votes, decisions;



function {:inline} Civl_InputOutputRelation_MAIN5(pids: Set_230) : bool
{
  (exists Civl_old_RequestChannel: [int]int, 
      Civl_old_DecisionChannel: [int][decision]int, 
      Civl_old_VoteChannel: [vote]int, 
      Civl_old_votes: [int]vote, 
      Civl_old_decisions: [int]decision, 
      Civl_RequestChannel: [int]int, 
      Civl_DecisionChannel: [int][decision]int, 
      Civl_VoteChannel: [vote]int, 
      Civl_votes: [int]vote, 
      Civl_decisions: [int]decision :: 
    Init(pids->val, 
        Civl_old_RequestChannel, 
        Civl_old_VoteChannel, 
        Civl_old_DecisionChannel, 
        Civl_old_decisions)
       && (((COMMIT() == COMMIT() ==> (forall i: int :: pid(i) ==> Civl_votes[i] == YES()))
           && (forall i: int :: i == 0 || pid(i) ==> Civl_decisions[i] == COMMIT()))
         || ((ABORT() == COMMIT() ==> (forall i: int :: pid(i) ==> Civl_votes[i] == YES()))
           && (forall i: int :: i == 0 || pid(i) ==> Civl_decisions[i] == ABORT()))))
}

implementation INV4(pids: Set_230) returns (Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int)
{
  var {:pool "INV4"} k: int;
  var pids': Set_230;
  var participantPids: Set_230;

  /*** structured program:
    assert Init(pids->val, RequestChannel, VoteChannel, DecisionChannel, decisions);
    assume {:add_to_pool "INV4", k, k + 1} {:add_to_pool "PARTICIPANT2", PARTICIPANT2(One_43(n))} 0 <= k && k <= n;
    havoc RequestChannel, VoteChannel, votes, decisions;
    assume (decisions[0] == COMMIT() || decisions[0] == ABORT())
       && (decisions[0] == COMMIT() ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
       && (forall i: int :: pidLe(i, k) ==> decisions[i] == decisions[0]);
    DecisionChannel := (lambda i: int :: 
      (lambda d: decision :: (if pidGt(i, k) && d == decisions[0] then 1 else 0)));
    pids' := pids;
    call participantPids := Set_Get_335(pids', (lambda i: int :: k < i && i <= n));
    call {:linear participantPids} create_asyncs_4801((lambda {:pool "PARTICIPANT2"} pa: PARTICIPANT2 :: pidGt(pa->pid->val, k)));
    call set_choice_4752(PARTICIPANT2(One_43(k + 1)));
  **** end structured program */

  anon0:
    assume Trigger_INV4_k(k);
    Civl_PAs_PARTICIPANT2 := MapConst_3_14186(0);
    assume {:add_to_pool "INV4", k, k + 1} {:add_to_pool "PARTICIPANT2", PARTICIPANT2(One_43(n))} 0 <= k && k <= n;
    havoc RequestChannel, VoteChannel, votes, decisions;
    assume (decisions[0] == COMMIT() || decisions[0] == ABORT())
       && (decisions[0] == COMMIT() ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
       && (forall i: int :: pidLe(i, k) ==> decisions[i] == decisions[0]);
    DecisionChannel := (lambda i: int :: 
      (lambda d: decision :: (if pidGt(i, k) && d == decisions[0] then 1 else 0)));
    pids' := pids;
    participantPids := Set_230((lambda i: int :: k < i && i <= n));
    pids' := Set_Difference_335(pids', participantPids);
    Civl_PAs_PARTICIPANT2 := MapAdd_14175(Civl_PAs_PARTICIPANT2, 
      MapIte_14193_3((lambda {:pool "PARTICIPANT2"} pa: PARTICIPANT2 :: pidGt(pa->pid->val, k)), 
        MapConst_3_14186(1), 
        MapConst_3_14186(0)));
    return;
}



procedure {:inline 1} INV4(pids: Set_230) returns (Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int);
  modifies RequestChannel, VoteChannel, DecisionChannel, votes, decisions;



function {:inline} Civl_InputOutputRelation_INV4(pids: Set_230, Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int) : bool
{
  (exists Civl_old_RequestChannel: [int]int, 
      Civl_old_DecisionChannel: [int][decision]int, 
      Civl_old_VoteChannel: [vote]int, 
      Civl_old_votes: [int]vote, 
      Civl_old_decisions: [int]decision, 
      Civl_RequestChannel: [int]int, 
      Civl_DecisionChannel: [int][decision]int, 
      Civl_VoteChannel: [vote]int, 
      Civl_votes: [int]vote, 
      Civl_decisions: [int]decision :: 
    (forall k: int :: 
        0 <= k && k <= n
           ==> (forall decisions: [int]decision, votes: [int]vote :: 
            (decisions[0] == COMMIT() || decisions[0] == ABORT())
                 && (decisions[0] == COMMIT() ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
                 && (forall i: int :: pidLe(i, k) ==> decisions[i] == decisions[0])
               ==> (forall Civl_pa1: PARTICIPANT2, Civl_pa2: PARTICIPANT2 :: 
                (lambda {:pool "PARTICIPANT2"} pa: PARTICIPANT2 :: pidGt(pa->pid->val, k))[Civl_pa1]
                     && (lambda {:pool "PARTICIPANT2"} pa: PARTICIPANT2 :: pidGt(pa->pid->val, k))[Civl_pa2]
                     && Civl_pa1 != Civl_pa2
                   ==> Civl_pa1->pid != Civl_pa2->pid)))
       && (forall k: int :: 
        0 <= k && k <= n
           ==> (forall decisions: [int]decision, votes: [int]vote :: 
            (decisions[0] == COMMIT() || decisions[0] == ABORT())
                 && (decisions[0] == COMMIT() ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
                 && (forall i: int :: pidLe(i, k) ==> decisions[i] == decisions[0])
               ==> (forall Civl_pa: PARTICIPANT2 :: 
                (lambda {:pool "PARTICIPANT2"} pa: PARTICIPANT2 :: pidGt(pa->pid->val, k))[Civl_pa]
                   ==> Set_Contains_43(Set_230((lambda i: int :: k < i && i <= n)), Civl_pa->pid->val))))
       && (forall k: int :: 
        0 <= k && k <= n
           ==> (forall decisions: [int]decision, votes: [int]vote :: 
            (decisions[0] == COMMIT() || decisions[0] == ABORT())
                 && (decisions[0] == COMMIT() ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
                 && (forall i: int :: pidLe(i, k) ==> decisions[i] == decisions[0])
               ==> Set_IsSubset_335(Set_230((lambda i: int :: k < i && i <= n)), pids)))
       && Init(pids->val, 
        Civl_old_RequestChannel, 
        Civl_old_VoteChannel, 
        Civl_old_DecisionChannel, 
        Civl_old_decisions)
       && (exists {:pool "INV4"} Civl_k#0: int :: 
        0 <= Civl_k#0
           && Civl_k#0 <= n
           && (Civl_decisions[0] == COMMIT() || Civl_decisions[0] == ABORT())
           && (Civl_decisions[0] == COMMIT()
             ==> (forall i: int :: pid(i) ==> Civl_votes[i] == YES()))
           && (forall i: int :: pidLe(i, Civl_k#0) ==> Civl_decisions[i] == Civl_decisions[0])
           && Civl_DecisionChannel
             == (lambda i: int :: 
              (lambda d: decision :: 
                (if pidGt(i, Civl_k#0) && d == Civl_decisions[0] then 1 else 0)))
           && Civl_PAs_PARTICIPANT2
             == MapAdd_14175(MapConst_3_14186(0), 
              MapIte_14193_3((lambda {:pool "PARTICIPANT2"} pa: PARTICIPANT2 :: 
                  pidGt(pa->pid->val, Civl_k#0)), 
                MapConst_3_14186(1), 
                MapConst_3_14186(0)))))
}

implementation INV4_With_Choice(pids: Set_230)
   returns (Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int, Civl_choice: Choice_INV4)
{
  var {:pool "INV4"} k: int;
  var pids': Set_230;
  var participantPids: Set_230;

  /*** structured program:
    assert Init(pids->val, RequestChannel, VoteChannel, DecisionChannel, decisions);
    assume {:add_to_pool "INV4", k, k + 1} {:add_to_pool "PARTICIPANT2", PARTICIPANT2(One_43(n))} 0 <= k && k <= n;
    havoc RequestChannel, VoteChannel, votes, decisions;
    assume (decisions[0] == COMMIT() || decisions[0] == ABORT())
       && (decisions[0] == COMMIT() ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
       && (forall i: int :: pidLe(i, k) ==> decisions[i] == decisions[0]);
    DecisionChannel := (lambda i: int :: 
      (lambda d: decision :: (if pidGt(i, k) && d == decisions[0] then 1 else 0)));
    pids' := pids;
    call participantPids := Set_Get_335(pids', (lambda i: int :: k < i && i <= n));
    call {:linear participantPids} create_asyncs_4801((lambda {:pool "PARTICIPANT2"} pa: PARTICIPANT2 :: pidGt(pa->pid->val, k)));
    call set_choice_4752(PARTICIPANT2(One_43(k + 1)));
  **** end structured program */

  anon0:
    Civl_PAs_PARTICIPANT2 := MapConst_3_14186(0);
    assert Init(pids->val, RequestChannel, VoteChannel, DecisionChannel, decisions);
    assume {:add_to_pool "INV4", k, k + 1} {:add_to_pool "PARTICIPANT2", PARTICIPANT2(One_43(n))} 0 <= k && k <= n;
    havoc RequestChannel, VoteChannel, votes, decisions;
    assume (decisions[0] == COMMIT() || decisions[0] == ABORT())
       && (decisions[0] == COMMIT() ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
       && (forall i: int :: pidLe(i, k) ==> decisions[i] == decisions[0]);
    DecisionChannel := (lambda i: int :: 
      (lambda d: decision :: (if pidGt(i, k) && d == decisions[0] then 1 else 0)));
    pids' := pids;
    participantPids := Set_230((lambda i: int :: k < i && i <= n));
    assert Set_IsSubset_335(participantPids, pids');
    pids' := Set_Difference_335(pids', participantPids);
    assert (forall Civl_pa: PARTICIPANT2 :: 
      (lambda {:pool "PARTICIPANT2"} pa: PARTICIPANT2 :: pidGt(pa->pid->val, k))[Civl_pa]
         ==> Set_Contains_43(participantPids, Civl_pa->pid->val));
    assert (forall Civl_pa1: PARTICIPANT2, Civl_pa2: PARTICIPANT2 :: 
      (lambda {:pool "PARTICIPANT2"} pa: PARTICIPANT2 :: pidGt(pa->pid->val, k))[Civl_pa1]
           && (lambda {:pool "PARTICIPANT2"} pa: PARTICIPANT2 :: pidGt(pa->pid->val, k))[Civl_pa2]
           && Civl_pa1 != Civl_pa2
         ==> Civl_pa1->pid != Civl_pa2->pid);
    Civl_PAs_PARTICIPANT2 := MapAdd_14175(Civl_PAs_PARTICIPANT2, 
      MapIte_14193_3((lambda {:pool "PARTICIPANT2"} pa: PARTICIPANT2 :: pidGt(pa->pid->val, k)), 
        MapConst_3_14186(1), 
        MapConst_3_14186(0)));
    assert Civl_PAs_PARTICIPANT2 == MapConst_3_14186(0)
       || Civl_PAs_PARTICIPANT2[PARTICIPANT2(One_43(k + 1))] > 0;
    Civl_choice->PARTICIPANT2 := PARTICIPANT2(One_43(k + 1));
    return;
}



procedure {:inline 1} INV4_With_Choice(pids: Set_230)
   returns (Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int, Civl_choice: Choice_INV4);
  modifies RequestChannel, VoteChannel, DecisionChannel, votes, decisions;



function {:inline} Civl_InputOutputRelation_INV4_With_Choice(pids: Set_230, 
    Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int, 
    Civl_choice: Choice_INV4)
   : bool
{
  (exists Civl_old_RequestChannel: [int]int, 
      Civl_old_DecisionChannel: [int][decision]int, 
      Civl_old_VoteChannel: [vote]int, 
      Civl_old_votes: [int]vote, 
      Civl_old_decisions: [int]decision, 
      Civl_RequestChannel: [int]int, 
      Civl_DecisionChannel: [int][decision]int, 
      Civl_VoteChannel: [vote]int, 
      Civl_votes: [int]vote, 
      Civl_decisions: [int]decision :: 
    (forall k: int :: 
        0 <= k && k <= n
           ==> (forall decisions: [int]decision, votes: [int]vote :: 
            (decisions[0] == COMMIT() || decisions[0] == ABORT())
                 && (decisions[0] == COMMIT() ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
                 && (forall i: int :: pidLe(i, k) ==> decisions[i] == decisions[0])
               ==> (forall Civl_pa1: PARTICIPANT2, Civl_pa2: PARTICIPANT2 :: 
                (lambda {:pool "PARTICIPANT2"} pa: PARTICIPANT2 :: pidGt(pa->pid->val, k))[Civl_pa1]
                     && (lambda {:pool "PARTICIPANT2"} pa: PARTICIPANT2 :: pidGt(pa->pid->val, k))[Civl_pa2]
                     && Civl_pa1 != Civl_pa2
                   ==> Civl_pa1->pid != Civl_pa2->pid)))
       && (forall k: int :: 
        0 <= k && k <= n
           ==> (forall decisions: [int]decision, votes: [int]vote :: 
            (decisions[0] == COMMIT() || decisions[0] == ABORT())
                 && (decisions[0] == COMMIT() ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
                 && (forall i: int :: pidLe(i, k) ==> decisions[i] == decisions[0])
               ==> (forall Civl_pa: PARTICIPANT2 :: 
                (lambda {:pool "PARTICIPANT2"} pa: PARTICIPANT2 :: pidGt(pa->pid->val, k))[Civl_pa]
                   ==> Set_Contains_43(Set_230((lambda i: int :: k < i && i <= n)), Civl_pa->pid->val))))
       && (forall k: int :: 
        0 <= k && k <= n
           ==> (forall decisions: [int]decision, votes: [int]vote :: 
            (decisions[0] == COMMIT() || decisions[0] == ABORT())
                 && (decisions[0] == COMMIT() ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
                 && (forall i: int :: pidLe(i, k) ==> decisions[i] == decisions[0])
               ==> Set_IsSubset_335(Set_230((lambda i: int :: k < i && i <= n)), pids)))
       && Init(pids->val, 
        Civl_old_RequestChannel, 
        Civl_old_VoteChannel, 
        Civl_old_DecisionChannel, 
        Civl_old_decisions)
       && (exists {:pool "INV4"} Civl_k#0: int :: 
        Init(pids->val, 
            Civl_old_RequestChannel, 
            Civl_old_VoteChannel, 
            Civl_old_DecisionChannel, 
            Civl_old_decisions)
           && 0 <= Civl_k#0
           && Civl_k#0 <= n
           && (Civl_decisions[0] == COMMIT() || Civl_decisions[0] == ABORT())
           && (Civl_decisions[0] == COMMIT()
             ==> (forall i: int :: pid(i) ==> Civl_votes[i] == YES()))
           && (forall i: int :: pidLe(i, Civl_k#0) ==> Civl_decisions[i] == Civl_decisions[0])
           && Set_IsSubset_335(Set_230((lambda i: int :: Civl_k#0 < i && i <= n)), pids)
           && (forall Civl_pa: PARTICIPANT2 :: 
            (lambda {:pool "PARTICIPANT2"} pa: PARTICIPANT2 :: 
                pidGt(pa->pid->val, Civl_k#0))[Civl_pa]
               ==> Set_Contains_43(Set_230((lambda i: int :: Civl_k#0 < i && i <= n)), Civl_pa->pid->val))
           && (forall Civl_pa1: PARTICIPANT2, Civl_pa2: PARTICIPANT2 :: 
            (lambda {:pool "PARTICIPANT2"} pa: PARTICIPANT2 :: 
                  pidGt(pa->pid->val, Civl_k#0))[Civl_pa1]
                 && (lambda {:pool "PARTICIPANT2"} pa: PARTICIPANT2 :: 
                  pidGt(pa->pid->val, Civl_k#0))[Civl_pa2]
                 && Civl_pa1 != Civl_pa2
               ==> Civl_pa1->pid != Civl_pa2->pid)
           && (Civl_PAs_PARTICIPANT2 == MapConst_3_14186(0)
             || Civl_PAs_PARTICIPANT2[PARTICIPANT2(One_43(Civl_k#0 + 1))] > 0)
           && Civl_DecisionChannel
             == (lambda i: int :: 
              (lambda d: decision :: 
                (if pidGt(i, Civl_k#0) && d == Civl_decisions[0] then 1 else 0)))
           && Civl_PAs_PARTICIPANT2
             == MapAdd_14175(MapConst_3_14186(0), 
              MapIte_14193_3((lambda {:pool "PARTICIPANT2"} pa: PARTICIPANT2 :: 
                  pidGt(pa->pid->val, Civl_k#0)), 
                MapConst_3_14186(1), 
                MapConst_3_14186(0)))
           && Civl_choice == Choice_INV4_PARTICIPANT2(PARTICIPANT2(One_43(Civl_k#0 + 1)))))
}

implementation INV2(pids: Set_230)
   returns (Civl_PAs_COORDINATOR2: [COORDINATOR2]int, 
    Civl_PAs_PARTICIPANT1: [PARTICIPANT1]int, 
    Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int)
{
  var pids': Set_230;
  var pid: One_43;
  var participantPids: Set_230;
  var {:pool "INV2"} k: int;

  /*** structured program:
    assert Init(pids->val, RequestChannel, VoteChannel, DecisionChannel, decisions);
    havoc RequestChannel, VoteChannel, votes;
    assume {:add_to_pool "INV2", k, k + 1} {:add_to_pool "PARTICIPANT1", PARTICIPANT1(One_43(n))} 0 <= k && k <= n;
    assume (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
       && VoteChannel[YES()] >= 0
       && VoteChannel[NO()] >= 0
       && VoteChannel[YES()] + VoteChannel[NO()] <= k
       && (VoteChannel[YES()] == k
         ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()));
    pids' := pids;
    call pid := One_Get_687(pids', 0);
    async call COORDINATOR2(pid);
    call participantPids := Set_Get_335(pids', (lambda i: int :: 1 <= i && i <= k));
    call {:linear participantPids} create_asyncs_4801((lambda pa: PARTICIPANT2 :: pidLe(pa->pid->val, k)));
    call participantPids := Set_Get_335(pids', (lambda i: int :: k < i && i <= n));
    call {:linear participantPids} create_asyncs_4825((lambda {:pool "PARTICIPANT1"} pa: PARTICIPANT1 :: pidGt(pa->pid->val, k)));
    call set_choice_4750(PARTICIPANT1(One_43(k + 1)));
  **** end structured program */

  anon0:
    assume Trigger_INV2_k(k);
    Civl_PAs_COORDINATOR2, Civl_PAs_PARTICIPANT1, Civl_PAs_PARTICIPANT2 := MapConst_3_14244(0), MapConst_3_14154(0), MapConst_3_14186(0);
    havoc RequestChannel, VoteChannel, votes;
    assume {:add_to_pool "INV2", k, k + 1} {:add_to_pool "PARTICIPANT1", PARTICIPANT1(One_43(n))} 0 <= k && k <= n;
    assume (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
       && VoteChannel[YES()] >= 0
       && VoteChannel[NO()] >= 0
       && VoteChannel[YES()] + VoteChannel[NO()] <= k
       && (VoteChannel[YES()] == k
         ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()));
    pids' := pids;
    pids' := Set_Remove_687(pids', 0);
    pid := One_43(0);
    Civl_PAs_COORDINATOR2 := MapAdd_14233(Civl_PAs_COORDINATOR2, MapConst_3_14244(0)[COORDINATOR2(pid) := 1]);
    participantPids := Set_230((lambda i: int :: 1 <= i && i <= k));
    pids' := Set_Difference_335(pids', participantPids);
    Civl_PAs_PARTICIPANT2 := MapAdd_14175(Civl_PAs_PARTICIPANT2, 
      MapIte_14193_3((lambda pa: PARTICIPANT2 :: pidLe(pa->pid->val, k)), 
        MapConst_3_14186(1), 
        MapConst_3_14186(0)));
    participantPids := Set_230((lambda i: int :: k < i && i <= n));
    pids' := Set_Difference_335(pids', participantPids);
    Civl_PAs_PARTICIPANT1 := MapAdd_14143(Civl_PAs_PARTICIPANT1, 
      MapIte_14161_3((lambda {:pool "PARTICIPANT1"} pa: PARTICIPANT1 :: pidGt(pa->pid->val, k)), 
        MapConst_3_14154(1), 
        MapConst_3_14154(0)));
    return;
}



procedure {:inline 1} INV2(pids: Set_230)
   returns (Civl_PAs_COORDINATOR2: [COORDINATOR2]int, 
    Civl_PAs_PARTICIPANT1: [PARTICIPANT1]int, 
    Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int);
  modifies RequestChannel, VoteChannel, votes;



function {:inline} Civl_InputOutputRelation_INV2(pids: Set_230, 
    Civl_PAs_COORDINATOR2: [COORDINATOR2]int, 
    Civl_PAs_PARTICIPANT1: [PARTICIPANT1]int, 
    Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int)
   : bool
{
  (exists Civl_old_RequestChannel: [int]int, 
      Civl_old_DecisionChannel: [int][decision]int, 
      Civl_old_VoteChannel: [vote]int, 
      Civl_old_votes: [int]vote, 
      Civl_old_decisions: [int]decision, 
      Civl_RequestChannel: [int]int, 
      Civl_DecisionChannel: [int][decision]int, 
      Civl_VoteChannel: [vote]int, 
      Civl_votes: [int]vote, 
      Civl_decisions: [int]decision :: 
    (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
        0 <= k && k <= n
           ==> 
          (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
             && VoteChannel[YES()] >= 0
             && VoteChannel[NO()] >= 0
             && VoteChannel[YES()] + VoteChannel[NO()] <= k
             && (VoteChannel[YES()] == k
               ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
           ==> (forall Civl_pa1: PARTICIPANT1, Civl_pa2: PARTICIPANT1 :: 
            (lambda {:pool "PARTICIPANT1"} pa: PARTICIPANT1 :: pidGt(pa->pid->val, k))[Civl_pa1]
                 && (lambda {:pool "PARTICIPANT1"} pa: PARTICIPANT1 :: pidGt(pa->pid->val, k))[Civl_pa2]
                 && Civl_pa1 != Civl_pa2
               ==> Civl_pa1->pid != Civl_pa2->pid))
       && (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
        0 <= k && k <= n
           ==> 
          (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
             && VoteChannel[YES()] >= 0
             && VoteChannel[NO()] >= 0
             && VoteChannel[YES()] + VoteChannel[NO()] <= k
             && (VoteChannel[YES()] == k
               ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
           ==> (forall Civl_pa: PARTICIPANT1 :: 
            (lambda {:pool "PARTICIPANT1"} pa: PARTICIPANT1 :: pidGt(pa->pid->val, k))[Civl_pa]
               ==> Set_Contains_43(Set_230((lambda i: int :: k < i && i <= n)), Civl_pa->pid->val)))
       && (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
        0 <= k && k <= n
           ==> 
          (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
             && VoteChannel[YES()] >= 0
             && VoteChannel[NO()] >= 0
             && VoteChannel[YES()] + VoteChannel[NO()] <= k
             && (VoteChannel[YES()] == k
               ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
           ==> Set_IsSubset_335(Set_230((lambda i: int :: k < i && i <= n)), 
            Set_Difference_335(Set_Remove_687(pids, 0), Set_230((lambda i: int :: 1 <= i && i <= k)))))
       && (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
        0 <= k && k <= n
           ==> 
          (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
             && VoteChannel[YES()] >= 0
             && VoteChannel[NO()] >= 0
             && VoteChannel[YES()] + VoteChannel[NO()] <= k
             && (VoteChannel[YES()] == k
               ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
           ==> (forall Civl_pa1: PARTICIPANT2, Civl_pa2: PARTICIPANT2 :: 
            (lambda pa: PARTICIPANT2 :: pidLe(pa->pid->val, k))[Civl_pa1]
                 && (lambda pa: PARTICIPANT2 :: pidLe(pa->pid->val, k))[Civl_pa2]
                 && Civl_pa1 != Civl_pa2
               ==> Civl_pa1->pid != Civl_pa2->pid))
       && (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
        0 <= k && k <= n
           ==> 
          (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
             && VoteChannel[YES()] >= 0
             && VoteChannel[NO()] >= 0
             && VoteChannel[YES()] + VoteChannel[NO()] <= k
             && (VoteChannel[YES()] == k
               ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
           ==> (forall Civl_pa: PARTICIPANT2 :: 
            (lambda pa: PARTICIPANT2 :: pidLe(pa->pid->val, k))[Civl_pa]
               ==> Set_Contains_43(Set_230((lambda i: int :: 1 <= i && i <= k)), Civl_pa->pid->val)))
       && (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
        0 <= k && k <= n
           ==> 
          (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
             && VoteChannel[YES()] >= 0
             && VoteChannel[NO()] >= 0
             && VoteChannel[YES()] + VoteChannel[NO()] <= k
             && (VoteChannel[YES()] == k
               ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
           ==> Set_IsSubset_335(Set_230((lambda i: int :: 1 <= i && i <= k)), Set_Remove_687(pids, 0)))
       && (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
        0 <= k && k <= n
           ==> 
          (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
             && VoteChannel[YES()] >= 0
             && VoteChannel[NO()] >= 0
             && VoteChannel[YES()] + VoteChannel[NO()] <= k
             && (VoteChannel[YES()] == k
               ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
           ==> Set_Contains_43(pids, 0))
       && Init(pids->val, 
        Civl_old_RequestChannel, 
        Civl_old_VoteChannel, 
        Civl_old_DecisionChannel, 
        Civl_old_decisions)
       && (exists {:pool "INV2"} Civl_k#0: int :: 
        0 <= Civl_k#0
           && Civl_k#0 <= n
           && (forall i: int :: pidGt(i, Civl_k#0) ==> Civl_RequestChannel[i] == 1)
           && Civl_VoteChannel[YES()] >= 0
           && Civl_VoteChannel[NO()] >= 0
           && Civl_VoteChannel[YES()] + Civl_VoteChannel[NO()] <= Civl_k#0
           && (Civl_VoteChannel[YES()] == Civl_k#0
             ==> (forall i: int :: pidLe(i, Civl_k#0) ==> Civl_votes[i] == YES()))
           && Civl_PAs_COORDINATOR2
             == MapAdd_14233(MapConst_3_14244(0), MapConst_3_14244(0)[COORDINATOR2(One_43(0)) := 1])
           && Civl_PAs_PARTICIPANT2
             == MapAdd_14175(MapConst_3_14186(0), 
              MapIte_14193_3((lambda pa: PARTICIPANT2 :: pidLe(pa->pid->val, Civl_k#0)), 
                MapConst_3_14186(1), 
                MapConst_3_14186(0)))
           && Civl_PAs_PARTICIPANT1
             == MapAdd_14143(MapConst_3_14154(0), 
              MapIte_14161_3((lambda {:pool "PARTICIPANT1"} pa: PARTICIPANT1 :: 
                  pidGt(pa->pid->val, Civl_k#0)), 
                MapConst_3_14154(1), 
                MapConst_3_14154(0)))))
}

implementation INV2_With_Choice(pids: Set_230)
   returns (Civl_PAs_COORDINATOR2: [COORDINATOR2]int, 
    Civl_PAs_PARTICIPANT1: [PARTICIPANT1]int, 
    Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int, 
    Civl_choice: Choice_INV2)
{
  var pids': Set_230;
  var pid: One_43;
  var participantPids: Set_230;
  var {:pool "INV2"} k: int;

  /*** structured program:
    assert Init(pids->val, RequestChannel, VoteChannel, DecisionChannel, decisions);
    havoc RequestChannel, VoteChannel, votes;
    assume {:add_to_pool "INV2", k, k + 1} {:add_to_pool "PARTICIPANT1", PARTICIPANT1(One_43(n))} 0 <= k && k <= n;
    assume (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
       && VoteChannel[YES()] >= 0
       && VoteChannel[NO()] >= 0
       && VoteChannel[YES()] + VoteChannel[NO()] <= k
       && (VoteChannel[YES()] == k
         ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()));
    pids' := pids;
    call pid := One_Get_687(pids', 0);
    async call COORDINATOR2(pid);
    call participantPids := Set_Get_335(pids', (lambda i: int :: 1 <= i && i <= k));
    call {:linear participantPids} create_asyncs_4801((lambda pa: PARTICIPANT2 :: pidLe(pa->pid->val, k)));
    call participantPids := Set_Get_335(pids', (lambda i: int :: k < i && i <= n));
    call {:linear participantPids} create_asyncs_4825((lambda {:pool "PARTICIPANT1"} pa: PARTICIPANT1 :: pidGt(pa->pid->val, k)));
    call set_choice_4750(PARTICIPANT1(One_43(k + 1)));
  **** end structured program */

  anon0:
    Civl_PAs_COORDINATOR2, Civl_PAs_PARTICIPANT1, Civl_PAs_PARTICIPANT2 := MapConst_3_14244(0), MapConst_3_14154(0), MapConst_3_14186(0);
    assert Init(pids->val, RequestChannel, VoteChannel, DecisionChannel, decisions);
    havoc RequestChannel, VoteChannel, votes;
    assume {:add_to_pool "INV2", k, k + 1} {:add_to_pool "PARTICIPANT1", PARTICIPANT1(One_43(n))} 0 <= k && k <= n;
    assume (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
       && VoteChannel[YES()] >= 0
       && VoteChannel[NO()] >= 0
       && VoteChannel[YES()] + VoteChannel[NO()] <= k
       && (VoteChannel[YES()] == k
         ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()));
    pids' := pids;
    assert Set_Contains_43(pids', 0);
    pids' := Set_Remove_687(pids', 0);
    pid := One_43(0);
    Civl_PAs_COORDINATOR2 := MapAdd_14233(Civl_PAs_COORDINATOR2, MapConst_3_14244(0)[COORDINATOR2(pid) := 1]);
    participantPids := Set_230((lambda i: int :: 1 <= i && i <= k));
    assert Set_IsSubset_335(participantPids, pids');
    pids' := Set_Difference_335(pids', participantPids);
    assert (forall Civl_pa: PARTICIPANT2 :: 
      (lambda pa: PARTICIPANT2 :: pidLe(pa->pid->val, k))[Civl_pa]
         ==> Set_Contains_43(participantPids, Civl_pa->pid->val));
    assert (forall Civl_pa1: PARTICIPANT2, Civl_pa2: PARTICIPANT2 :: 
      (lambda pa: PARTICIPANT2 :: pidLe(pa->pid->val, k))[Civl_pa1]
           && (lambda pa: PARTICIPANT2 :: pidLe(pa->pid->val, k))[Civl_pa2]
           && Civl_pa1 != Civl_pa2
         ==> Civl_pa1->pid != Civl_pa2->pid);
    Civl_PAs_PARTICIPANT2 := MapAdd_14175(Civl_PAs_PARTICIPANT2, 
      MapIte_14193_3((lambda pa: PARTICIPANT2 :: pidLe(pa->pid->val, k)), 
        MapConst_3_14186(1), 
        MapConst_3_14186(0)));
    participantPids := Set_230((lambda i: int :: k < i && i <= n));
    assert Set_IsSubset_335(participantPids, pids');
    pids' := Set_Difference_335(pids', participantPids);
    assert (forall Civl_pa: PARTICIPANT1 :: 
      (lambda {:pool "PARTICIPANT1"} pa: PARTICIPANT1 :: pidGt(pa->pid->val, k))[Civl_pa]
         ==> Set_Contains_43(participantPids, Civl_pa->pid->val));
    assert (forall Civl_pa1: PARTICIPANT1, Civl_pa2: PARTICIPANT1 :: 
      (lambda {:pool "PARTICIPANT1"} pa: PARTICIPANT1 :: pidGt(pa->pid->val, k))[Civl_pa1]
           && (lambda {:pool "PARTICIPANT1"} pa: PARTICIPANT1 :: pidGt(pa->pid->val, k))[Civl_pa2]
           && Civl_pa1 != Civl_pa2
         ==> Civl_pa1->pid != Civl_pa2->pid);
    Civl_PAs_PARTICIPANT1 := MapAdd_14143(Civl_PAs_PARTICIPANT1, 
      MapIte_14161_3((lambda {:pool "PARTICIPANT1"} pa: PARTICIPANT1 :: pidGt(pa->pid->val, k)), 
        MapConst_3_14154(1), 
        MapConst_3_14154(0)));
    assert Civl_PAs_PARTICIPANT1 == MapConst_3_14154(0)
       || Civl_PAs_PARTICIPANT1[PARTICIPANT1(One_43(k + 1))] > 0;
    Civl_choice->PARTICIPANT1 := PARTICIPANT1(One_43(k + 1));
    return;
}



procedure {:inline 1} INV2_With_Choice(pids: Set_230)
   returns (Civl_PAs_COORDINATOR2: [COORDINATOR2]int, 
    Civl_PAs_PARTICIPANT1: [PARTICIPANT1]int, 
    Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int, 
    Civl_choice: Choice_INV2);
  modifies RequestChannel, VoteChannel, votes;



function {:inline} Civl_InputOutputRelation_INV2_With_Choice(pids: Set_230, 
    Civl_PAs_COORDINATOR2: [COORDINATOR2]int, 
    Civl_PAs_PARTICIPANT1: [PARTICIPANT1]int, 
    Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int, 
    Civl_choice: Choice_INV2)
   : bool
{
  (exists Civl_old_RequestChannel: [int]int, 
      Civl_old_DecisionChannel: [int][decision]int, 
      Civl_old_VoteChannel: [vote]int, 
      Civl_old_votes: [int]vote, 
      Civl_old_decisions: [int]decision, 
      Civl_RequestChannel: [int]int, 
      Civl_DecisionChannel: [int][decision]int, 
      Civl_VoteChannel: [vote]int, 
      Civl_votes: [int]vote, 
      Civl_decisions: [int]decision :: 
    (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
        0 <= k && k <= n
           ==> 
          (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
             && VoteChannel[YES()] >= 0
             && VoteChannel[NO()] >= 0
             && VoteChannel[YES()] + VoteChannel[NO()] <= k
             && (VoteChannel[YES()] == k
               ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
           ==> (forall Civl_pa1: PARTICIPANT1, Civl_pa2: PARTICIPANT1 :: 
            (lambda {:pool "PARTICIPANT1"} pa: PARTICIPANT1 :: pidGt(pa->pid->val, k))[Civl_pa1]
                 && (lambda {:pool "PARTICIPANT1"} pa: PARTICIPANT1 :: pidGt(pa->pid->val, k))[Civl_pa2]
                 && Civl_pa1 != Civl_pa2
               ==> Civl_pa1->pid != Civl_pa2->pid))
       && (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
        0 <= k && k <= n
           ==> 
          (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
             && VoteChannel[YES()] >= 0
             && VoteChannel[NO()] >= 0
             && VoteChannel[YES()] + VoteChannel[NO()] <= k
             && (VoteChannel[YES()] == k
               ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
           ==> (forall Civl_pa: PARTICIPANT1 :: 
            (lambda {:pool "PARTICIPANT1"} pa: PARTICIPANT1 :: pidGt(pa->pid->val, k))[Civl_pa]
               ==> Set_Contains_43(Set_230((lambda i: int :: k < i && i <= n)), Civl_pa->pid->val)))
       && (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
        0 <= k && k <= n
           ==> 
          (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
             && VoteChannel[YES()] >= 0
             && VoteChannel[NO()] >= 0
             && VoteChannel[YES()] + VoteChannel[NO()] <= k
             && (VoteChannel[YES()] == k
               ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
           ==> Set_IsSubset_335(Set_230((lambda i: int :: k < i && i <= n)), 
            Set_Difference_335(Set_Remove_687(pids, 0), Set_230((lambda i: int :: 1 <= i && i <= k)))))
       && (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
        0 <= k && k <= n
           ==> 
          (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
             && VoteChannel[YES()] >= 0
             && VoteChannel[NO()] >= 0
             && VoteChannel[YES()] + VoteChannel[NO()] <= k
             && (VoteChannel[YES()] == k
               ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
           ==> (forall Civl_pa1: PARTICIPANT2, Civl_pa2: PARTICIPANT2 :: 
            (lambda pa: PARTICIPANT2 :: pidLe(pa->pid->val, k))[Civl_pa1]
                 && (lambda pa: PARTICIPANT2 :: pidLe(pa->pid->val, k))[Civl_pa2]
                 && Civl_pa1 != Civl_pa2
               ==> Civl_pa1->pid != Civl_pa2->pid))
       && (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
        0 <= k && k <= n
           ==> 
          (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
             && VoteChannel[YES()] >= 0
             && VoteChannel[NO()] >= 0
             && VoteChannel[YES()] + VoteChannel[NO()] <= k
             && (VoteChannel[YES()] == k
               ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
           ==> (forall Civl_pa: PARTICIPANT2 :: 
            (lambda pa: PARTICIPANT2 :: pidLe(pa->pid->val, k))[Civl_pa]
               ==> Set_Contains_43(Set_230((lambda i: int :: 1 <= i && i <= k)), Civl_pa->pid->val)))
       && (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
        0 <= k && k <= n
           ==> 
          (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
             && VoteChannel[YES()] >= 0
             && VoteChannel[NO()] >= 0
             && VoteChannel[YES()] + VoteChannel[NO()] <= k
             && (VoteChannel[YES()] == k
               ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
           ==> Set_IsSubset_335(Set_230((lambda i: int :: 1 <= i && i <= k)), Set_Remove_687(pids, 0)))
       && (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
        0 <= k && k <= n
           ==> 
          (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
             && VoteChannel[YES()] >= 0
             && VoteChannel[NO()] >= 0
             && VoteChannel[YES()] + VoteChannel[NO()] <= k
             && (VoteChannel[YES()] == k
               ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
           ==> Set_Contains_43(pids, 0))
       && Init(pids->val, 
        Civl_old_RequestChannel, 
        Civl_old_VoteChannel, 
        Civl_old_DecisionChannel, 
        Civl_old_decisions)
       && (exists {:pool "INV2"} Civl_k#0: int :: 
        Init(pids->val, 
            Civl_old_RequestChannel, 
            Civl_old_VoteChannel, 
            Civl_DecisionChannel, 
            Civl_decisions)
           && 0 <= Civl_k#0
           && Civl_k#0 <= n
           && (forall i: int :: pidGt(i, Civl_k#0) ==> Civl_RequestChannel[i] == 1)
           && Civl_VoteChannel[YES()] >= 0
           && Civl_VoteChannel[NO()] >= 0
           && Civl_VoteChannel[YES()] + Civl_VoteChannel[NO()] <= Civl_k#0
           && (Civl_VoteChannel[YES()] == Civl_k#0
             ==> (forall i: int :: pidLe(i, Civl_k#0) ==> Civl_votes[i] == YES()))
           && Set_Contains_43(pids, 0)
           && Set_IsSubset_335(Set_230((lambda i: int :: 1 <= i && i <= Civl_k#0)), Set_Remove_687(pids, 0))
           && (forall Civl_pa: PARTICIPANT2 :: 
            (lambda pa: PARTICIPANT2 :: pidLe(pa->pid->val, Civl_k#0))[Civl_pa]
               ==> Set_Contains_43(Set_230((lambda i: int :: 1 <= i && i <= Civl_k#0)), Civl_pa->pid->val))
           && (forall Civl_pa1: PARTICIPANT2, Civl_pa2: PARTICIPANT2 :: 
            (lambda pa: PARTICIPANT2 :: pidLe(pa->pid->val, Civl_k#0))[Civl_pa1]
                 && (lambda pa: PARTICIPANT2 :: pidLe(pa->pid->val, Civl_k#0))[Civl_pa2]
                 && Civl_pa1 != Civl_pa2
               ==> Civl_pa1->pid != Civl_pa2->pid)
           && Set_IsSubset_335(Set_230((lambda i: int :: Civl_k#0 < i && i <= n)), 
            Set_Difference_335(Set_Remove_687(pids, 0), Set_230((lambda i: int :: 1 <= i && i <= Civl_k#0))))
           && (forall Civl_pa: PARTICIPANT1 :: 
            (lambda {:pool "PARTICIPANT1"} pa: PARTICIPANT1 :: 
                pidGt(pa->pid->val, Civl_k#0))[Civl_pa]
               ==> Set_Contains_43(Set_230((lambda i: int :: Civl_k#0 < i && i <= n)), Civl_pa->pid->val))
           && (forall Civl_pa1: PARTICIPANT1, Civl_pa2: PARTICIPANT1 :: 
            (lambda {:pool "PARTICIPANT1"} pa: PARTICIPANT1 :: 
                  pidGt(pa->pid->val, Civl_k#0))[Civl_pa1]
                 && (lambda {:pool "PARTICIPANT1"} pa: PARTICIPANT1 :: 
                  pidGt(pa->pid->val, Civl_k#0))[Civl_pa2]
                 && Civl_pa1 != Civl_pa2
               ==> Civl_pa1->pid != Civl_pa2->pid)
           && (Civl_PAs_PARTICIPANT1 == MapConst_3_14154(0)
             || Civl_PAs_PARTICIPANT1[PARTICIPANT1(One_43(Civl_k#0 + 1))] > 0)
           && Civl_PAs_COORDINATOR2
             == MapAdd_14233(MapConst_3_14244(0), MapConst_3_14244(0)[COORDINATOR2(One_43(0)) := 1])
           && Civl_PAs_PARTICIPANT2
             == MapAdd_14175(MapConst_3_14186(0), 
              MapIte_14193_3((lambda pa: PARTICIPANT2 :: pidLe(pa->pid->val, Civl_k#0)), 
                MapConst_3_14186(1), 
                MapConst_3_14186(0)))
           && Civl_PAs_PARTICIPANT1
             == MapAdd_14143(MapConst_3_14154(0), 
              MapIte_14161_3((lambda {:pool "PARTICIPANT1"} pa: PARTICIPANT1 :: 
                  pidGt(pa->pid->val, Civl_k#0)), 
                MapConst_3_14154(1), 
                MapConst_3_14154(0)))
           && Civl_choice == Choice_INV2_PARTICIPANT1(PARTICIPANT1(One_43(Civl_k#0 + 1)))))
}

implementation PARTICIPANT1(pid: One_43) returns (Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int)
{
  var v: vote;

  /*** structured program:
    assert pid(pid->val);
    if (*)
    {
        assume RequestChannel[pid->val] > 0;
        RequestChannel[pid->val] := RequestChannel[pid->val] - 1;
        if (*)
        {
            v := YES();
        }
        else
        {
            v := NO();
        }

        votes[pid->val] := v;
        VoteChannel[v] := VoteChannel[v] + 1;
    }

    async call PARTICIPANT2(pid);
  **** end structured program */

  anon0:
    Civl_PAs_PARTICIPANT2 := MapConst_3_14186(0);
    goto anon6_Then, anon6_Else;

  anon6_Else:
    goto anon5;

  anon5:
    Civl_PAs_PARTICIPANT2 := MapAdd_14175(Civl_PAs_PARTICIPANT2, MapConst_3_14186(0)[PARTICIPANT2(pid) := 1]);
    return;

  anon6_Then:
    assume RequestChannel[pid->val] > 0;
    RequestChannel[pid->val] := RequestChannel[pid->val] - 1;
    goto anon7_Then, anon7_Else;

  anon7_Else:
    v := NO();
    goto anon4;

  anon4:
    votes[pid->val] := v;
    VoteChannel[v] := VoteChannel[v] + 1;
    goto anon5;

  anon7_Then:
    v := YES();
    goto anon4;
}



procedure {:inline 1} PARTICIPANT1(pid: One_43) returns (Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int);
  modifies RequestChannel, VoteChannel, votes;



function {:inline} Civl_InputOutputRelation_PARTICIPANT1(pid: One_43, Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int) : bool
{
  (exists Civl_old_RequestChannel: [int]int, 
      Civl_old_DecisionChannel: [int][decision]int, 
      Civl_old_VoteChannel: [vote]int, 
      Civl_old_votes: [int]vote, 
      Civl_old_decisions: [int]decision, 
      Civl_RequestChannel: [int]int, 
      Civl_DecisionChannel: [int][decision]int, 
      Civl_VoteChannel: [vote]int, 
      Civl_votes: [int]vote, 
      Civl_decisions: [int]decision :: 
    pid(pid->val)
       && (
        (
          Civl_old_RequestChannel[pid->val] > 0
           && Civl_RequestChannel
             == Civl_old_RequestChannel[pid->val := Civl_old_RequestChannel[pid->val] - 1]
           && Civl_votes == Civl_old_votes[pid->val := YES()]
           && Civl_VoteChannel
             == Civl_old_VoteChannel[YES() := Civl_old_VoteChannel[YES()] + 1]
           && Civl_PAs_PARTICIPANT2
             == MapAdd_14175(MapConst_3_14186(0), MapConst_3_14186(0)[PARTICIPANT2(pid) := 1]))
         || (
          Civl_old_RequestChannel[pid->val] > 0
           && Civl_RequestChannel
             == Civl_old_RequestChannel[pid->val := Civl_old_RequestChannel[pid->val] - 1]
           && Civl_votes == Civl_old_votes[pid->val := NO()]
           && Civl_VoteChannel == Civl_old_VoteChannel[NO() := Civl_old_VoteChannel[NO()] + 1]
           && Civl_PAs_PARTICIPANT2
             == MapAdd_14175(MapConst_3_14186(0), MapConst_3_14186(0)[PARTICIPANT2(pid) := 1]))
         || (
          Civl_PAs_PARTICIPANT2
             == MapAdd_14175(MapConst_3_14186(0), MapConst_3_14186(0)[PARTICIPANT2(pid) := 1])
           && Civl_RequestChannel == Civl_old_RequestChannel
           && Civl_VoteChannel == Civl_old_VoteChannel
           && Civl_votes == Civl_old_votes)))
}

implementation PARTICIPANT2(pid: One_43)
{
  var d: decision;

  /*** structured program:
    assert pid(pid->val);
    assert DecisionChannel[pid->val][NONE()] == 0;
    if (*)
    {
        d := COMMIT();
    }
    else
    {
        d := ABORT();
    }

    assume DecisionChannel[pid->val][d] > 0;
    DecisionChannel[pid->val][d] := DecisionChannel[pid->val][d] - 1;
    decisions[pid->val] := d;
  **** end structured program */

  anon0:
    goto anon4_Then, anon4_Else;

  anon4_Else:
    d := ABORT();
    goto anon3;

  anon3:
    assume DecisionChannel[pid->val][d] > 0;
    DecisionChannel[pid->val][d] := DecisionChannel[pid->val][d] - 1;
    decisions[pid->val] := d;
    return;

  anon4_Then:
    d := COMMIT();
    goto anon3;
}



procedure {:inline 1} PARTICIPANT2(pid: One_43);
  modifies DecisionChannel, decisions;



function {:inline} Civl_InputOutputRelation_PARTICIPANT2(pid: One_43) : bool
{
  (exists Civl_old_RequestChannel: [int]int, 
      Civl_old_DecisionChannel: [int][decision]int, 
      Civl_old_VoteChannel: [vote]int, 
      Civl_old_votes: [int]vote, 
      Civl_old_decisions: [int]decision, 
      Civl_RequestChannel: [int]int, 
      Civl_DecisionChannel: [int][decision]int, 
      Civl_VoteChannel: [vote]int, 
      Civl_votes: [int]vote, 
      Civl_decisions: [int]decision :: 
    Civl_old_DecisionChannel[pid->val][NONE()] == 0
       && pid(pid->val)
       && ((
          Civl_old_DecisionChannel[pid->val][COMMIT()] > 0
           && Civl_DecisionChannel
             == Civl_old_DecisionChannel[pid->val := Civl_old_DecisionChannel[pid->val][COMMIT() := Civl_old_DecisionChannel[pid->val][COMMIT()] - 1]]
           && Civl_decisions == Civl_old_decisions[pid->val := COMMIT()])
         || (
          Civl_old_DecisionChannel[pid->val][ABORT()] > 0
           && Civl_DecisionChannel
             == Civl_old_DecisionChannel[pid->val := Civl_old_DecisionChannel[pid->val][ABORT() := Civl_old_DecisionChannel[pid->val][ABORT()] - 1]]
           && Civl_decisions == Civl_old_decisions[pid->val := ABORT()])))
}

implementation COORDINATOR1(pid: One_43) returns (Civl_PAs_COORDINATOR2: [COORDINATOR2]int)
{
  /*** structured program:
    assert pid->val == 0;
    RequestChannel := (lambda i: int :: (if pid(i) then RequestChannel[i] + 1 else RequestChannel[i]));
    async call COORDINATOR2(pid);
  **** end structured program */

  anon0:
    Civl_PAs_COORDINATOR2 := MapConst_3_14244(0);
    RequestChannel := (lambda i: int :: (if pid(i) then RequestChannel[i] + 1 else RequestChannel[i]));
    Civl_PAs_COORDINATOR2 := MapAdd_14233(Civl_PAs_COORDINATOR2, MapConst_3_14244(0)[COORDINATOR2(pid) := 1]);
    return;
}



procedure {:inline 1} COORDINATOR1(pid: One_43) returns (Civl_PAs_COORDINATOR2: [COORDINATOR2]int);
  modifies RequestChannel;



function {:inline} Civl_InputOutputRelation_COORDINATOR1(pid: One_43, Civl_PAs_COORDINATOR2: [COORDINATOR2]int) : bool
{
  (exists Civl_old_RequestChannel: [int]int, 
      Civl_old_DecisionChannel: [int][decision]int, 
      Civl_old_VoteChannel: [vote]int, 
      Civl_old_votes: [int]vote, 
      Civl_old_decisions: [int]decision, 
      Civl_RequestChannel: [int]int, 
      Civl_DecisionChannel: [int][decision]int, 
      Civl_VoteChannel: [vote]int, 
      Civl_votes: [int]vote, 
      Civl_decisions: [int]decision :: 
    pid->val == 0
       && 
      Civl_RequestChannel
         == (lambda i: int :: 
          (if pid(i) then Civl_old_RequestChannel[i] + 1 else Civl_old_RequestChannel[i]))
       && Civl_PAs_COORDINATOR2
         == MapAdd_14233(MapConst_3_14244(0), MapConst_3_14244(0)[COORDINATOR2(pid) := 1]))
}

implementation COORDINATOR2(pid: One_43)
{
  var dec: decision;

  /*** structured program:
    assert pid->val == 0;
    if (*)
    {
        assume VoteChannel[YES()] >= n;
        dec := COMMIT();
    }
    else
    {
        dec := ABORT();
    }

    decisions[pid->val] := dec;
    havoc VoteChannel;
    DecisionChannel := (lambda i: int :: 
      (lambda d: decision :: 
        (if pid(i) && d == dec
           then DecisionChannel[i][d] + 1
           else DecisionChannel[i][d])));
  **** end structured program */

  anon0:
    goto anon4_Then, anon4_Else;

  anon4_Else:
    dec := ABORT();
    goto anon3;

  anon3:
    decisions[pid->val] := dec;
    havoc VoteChannel;
    DecisionChannel := (lambda i: int :: 
      (lambda d: decision :: 
        (if pid(i) && d == dec
           then DecisionChannel[i][d] + 1
           else DecisionChannel[i][d])));
    return;

  anon4_Then:
    assume VoteChannel[YES()] >= n;
    dec := COMMIT();
    goto anon3;
}



procedure {:inline 1} COORDINATOR2(pid: One_43);
  modifies VoteChannel, DecisionChannel, decisions;



function {:inline} Civl_InputOutputRelation_COORDINATOR2(pid: One_43) : bool
{
  (exists Civl_old_RequestChannel: [int]int, 
      Civl_old_DecisionChannel: [int][decision]int, 
      Civl_old_VoteChannel: [vote]int, 
      Civl_old_votes: [int]vote, 
      Civl_old_decisions: [int]decision, 
      Civl_RequestChannel: [int]int, 
      Civl_DecisionChannel: [int][decision]int, 
      Civl_VoteChannel: [vote]int, 
      Civl_votes: [int]vote, 
      Civl_decisions: [int]decision :: 
    pid->val == 0
       && ((
          Civl_old_VoteChannel[YES()] >= n
           && Civl_decisions == Civl_old_decisions[pid->val := COMMIT()]
           && Civl_DecisionChannel
             == (lambda i: int :: 
              (lambda d: decision :: 
                (if pid(i) && d == COMMIT()
                   then Civl_old_DecisionChannel[i][d] + 1
                   else Civl_old_DecisionChannel[i][d]))))
         || (Civl_decisions == Civl_old_decisions[pid->val := ABORT()]
           && Civl_DecisionChannel
             == (lambda i: int :: 
              (lambda d: decision :: 
                (if pid(i) && d == ABORT()
                   then Civl_old_DecisionChannel[i][d] + 1
                   else Civl_old_DecisionChannel[i][d]))))))
}

implementation SET_VOTE(pid: One_43, v: vote)
{
  /*** structured program:
    votes[pid->val] := v;
  **** end structured program */

  anon0:
    votes[pid->val] := v;
    return;
}



procedure {:inline 1} SET_VOTE(pid: One_43, v: vote);
  modifies votes;



function {:inline} Civl_InputOutputRelation_SET_VOTE(pid: One_43, v: vote) : bool
{
  (exists Civl_old_RequestChannel: [int]int, 
      Civl_old_DecisionChannel: [int][decision]int, 
      Civl_old_VoteChannel: [vote]int, 
      Civl_old_votes: [int]vote, 
      Civl_old_decisions: [int]decision, 
      Civl_RequestChannel: [int]int, 
      Civl_DecisionChannel: [int][decision]int, 
      Civl_VoteChannel: [vote]int, 
      Civl_votes: [int]vote, 
      Civl_decisions: [int]decision :: 
    Civl_votes == Civl_old_votes[pid->val := v])
}

implementation SET_DECISION(pid: One_43, d: decision)
{
  /*** structured program:
    decisions[pid->val] := d;
  **** end structured program */

  anon0:
    decisions[pid->val] := d;
    return;
}



procedure {:inline 1} SET_DECISION(pid: One_43, d: decision);
  modifies decisions;



function {:inline} Civl_InputOutputRelation_SET_DECISION(pid: One_43, d: decision) : bool
{
  (exists Civl_old_RequestChannel: [int]int, 
      Civl_old_DecisionChannel: [int][decision]int, 
      Civl_old_VoteChannel: [vote]int, 
      Civl_old_votes: [int]vote, 
      Civl_old_decisions: [int]decision, 
      Civl_RequestChannel: [int]int, 
      Civl_DecisionChannel: [int][decision]int, 
      Civl_VoteChannel: [vote]int, 
      Civl_votes: [int]vote, 
      Civl_decisions: [int]decision :: 
    Civl_decisions == Civl_old_decisions[pid->val := d])
}

implementation SEND_REQUEST(pid: int)
{
  /*** structured program:
    RequestChannel[pid] := RequestChannel[pid] + 1;
  **** end structured program */

  anon0:
    RequestChannel[pid] := RequestChannel[pid] + 1;
    return;
}



procedure {:inline 1} SEND_REQUEST(pid: int);
  modifies RequestChannel;



function {:inline} Civl_InputOutputRelation_SEND_REQUEST(pid: int) : bool
{
  (exists Civl_old_RequestChannel: [int]int, 
      Civl_old_DecisionChannel: [int][decision]int, 
      Civl_old_VoteChannel: [vote]int, 
      Civl_old_votes: [int]vote, 
      Civl_old_decisions: [int]decision, 
      Civl_RequestChannel: [int]int, 
      Civl_DecisionChannel: [int][decision]int, 
      Civl_VoteChannel: [vote]int, 
      Civl_votes: [int]vote, 
      Civl_decisions: [int]decision :: 
    Civl_RequestChannel
       == Civl_old_RequestChannel[pid := Civl_old_RequestChannel[pid] + 1])
}

implementation RECEIVE_REQ(pid: int)
{
  /*** structured program:
    assume RequestChannel[pid] > 0;
    RequestChannel[pid] := RequestChannel[pid] - 1;
  **** end structured program */

  anon0:
    assume RequestChannel[pid] > 0;
    RequestChannel[pid] := RequestChannel[pid] - 1;
    return;
}



procedure {:inline 1} RECEIVE_REQ(pid: int);
  modifies RequestChannel;



function {:inline} Civl_InputOutputRelation_RECEIVE_REQ(pid: int) : bool
{
  (exists Civl_old_RequestChannel: [int]int, 
      Civl_old_DecisionChannel: [int][decision]int, 
      Civl_old_VoteChannel: [vote]int, 
      Civl_old_votes: [int]vote, 
      Civl_old_decisions: [int]decision, 
      Civl_RequestChannel: [int]int, 
      Civl_DecisionChannel: [int][decision]int, 
      Civl_VoteChannel: [vote]int, 
      Civl_votes: [int]vote, 
      Civl_decisions: [int]decision :: 
    Civl_old_RequestChannel[pid] > 0
       && Civl_RequestChannel
         == Civl_old_RequestChannel[pid := Civl_old_RequestChannel[pid] - 1])
}

implementation SEND_VOTE(v: vote)
{
  /*** structured program:
    VoteChannel[v] := VoteChannel[v] + 1;
  **** end structured program */

  anon0:
    VoteChannel[v] := VoteChannel[v] + 1;
    return;
}



procedure {:inline 1} SEND_VOTE(v: vote);
  modifies VoteChannel;



function {:inline} Civl_InputOutputRelation_SEND_VOTE(v: vote) : bool
{
  (exists Civl_old_RequestChannel: [int]int, 
      Civl_old_DecisionChannel: [int][decision]int, 
      Civl_old_VoteChannel: [vote]int, 
      Civl_old_votes: [int]vote, 
      Civl_old_decisions: [int]decision, 
      Civl_RequestChannel: [int]int, 
      Civl_DecisionChannel: [int][decision]int, 
      Civl_VoteChannel: [vote]int, 
      Civl_votes: [int]vote, 
      Civl_decisions: [int]decision :: 
    Civl_VoteChannel == Civl_old_VoteChannel[v := Civl_old_VoteChannel[v] + 1])
}

implementation RECEIVE_VOTE() returns (v: vote)
{
  /*** structured program:
    assume VoteChannel[v] > 0;
    VoteChannel[v] := VoteChannel[v] - 1;
  **** end structured program */

  anon0:
    assume VoteChannel[v] > 0;
    VoteChannel[v] := VoteChannel[v] - 1;
    return;
}



procedure {:inline 1} RECEIVE_VOTE() returns (v: vote);
  modifies VoteChannel;



function {:inline} Civl_InputOutputRelation_RECEIVE_VOTE(v: vote) : bool
{
  (exists Civl_old_RequestChannel: [int]int, 
      Civl_old_DecisionChannel: [int][decision]int, 
      Civl_old_VoteChannel: [vote]int, 
      Civl_old_votes: [int]vote, 
      Civl_old_decisions: [int]decision, 
      Civl_RequestChannel: [int]int, 
      Civl_DecisionChannel: [int][decision]int, 
      Civl_VoteChannel: [vote]int, 
      Civl_votes: [int]vote, 
      Civl_decisions: [int]decision :: 
    Civl_old_VoteChannel[v] > 0
       && Civl_VoteChannel == Civl_old_VoteChannel[v := Civl_old_VoteChannel[v] - 1])
}

implementation SEND_DECISION(pid: int, d: decision)
{
  /*** structured program:
    DecisionChannel[pid][d] := DecisionChannel[pid][d] + 1;
  **** end structured program */

  anon0:
    DecisionChannel[pid][d] := DecisionChannel[pid][d] + 1;
    return;
}



procedure {:inline 1} SEND_DECISION(pid: int, d: decision);
  modifies DecisionChannel;



function {:inline} Civl_InputOutputRelation_SEND_DECISION(pid: int, d: decision) : bool
{
  (exists Civl_old_RequestChannel: [int]int, 
      Civl_old_DecisionChannel: [int][decision]int, 
      Civl_old_VoteChannel: [vote]int, 
      Civl_old_votes: [int]vote, 
      Civl_old_decisions: [int]decision, 
      Civl_RequestChannel: [int]int, 
      Civl_DecisionChannel: [int][decision]int, 
      Civl_VoteChannel: [vote]int, 
      Civl_votes: [int]vote, 
      Civl_decisions: [int]decision :: 
    Civl_DecisionChannel
       == Civl_old_DecisionChannel[pid := Civl_old_DecisionChannel[pid][d := Civl_old_DecisionChannel[pid][d] + 1]])
}

implementation RECEIVE_DECISION(pid: int) returns (d: decision)
{
  /*** structured program:
    assume DecisionChannel[pid][d] > 0;
    DecisionChannel[pid][d] := DecisionChannel[pid][d] - 1;
  **** end structured program */

  anon0:
    assume DecisionChannel[pid][d] > 0;
    DecisionChannel[pid][d] := DecisionChannel[pid][d] - 1;
    return;
}



procedure {:inline 1} RECEIVE_DECISION(pid: int) returns (d: decision);
  modifies DecisionChannel;



function {:inline} Civl_InputOutputRelation_RECEIVE_DECISION(pid: int, d: decision) : bool
{
  (exists Civl_old_RequestChannel: [int]int, 
      Civl_old_DecisionChannel: [int][decision]int, 
      Civl_old_VoteChannel: [vote]int, 
      Civl_old_votes: [int]vote, 
      Civl_old_decisions: [int]decision, 
      Civl_RequestChannel: [int]int, 
      Civl_DecisionChannel: [int][decision]int, 
      Civl_VoteChannel: [vote]int, 
      Civl_votes: [int]vote, 
      Civl_decisions: [int]decision :: 
    Civl_old_DecisionChannel[pid][d] > 0
       && Civl_DecisionChannel
         == Civl_old_DecisionChannel[pid := Civl_old_DecisionChannel[pid][d := Civl_old_DecisionChannel[pid][d] - 1]])
}

implementation Civl_Skip()
{

  init:
    return;
}



pure procedure {:inline 1} Civl_Skip();



function {:inline} Civl_InputOutputRelation_Civl_Skip() : bool
{
  (exists Civl_old_RequestChannel: [int]int, 
      Civl_old_DecisionChannel: [int][decision]int, 
      Civl_old_VoteChannel: [vote]int, 
      Civl_old_votes: [int]vote, 
      Civl_old_decisions: [int]decision, 
      Civl_RequestChannel: [int]int, 
      Civl_DecisionChannel: [int][decision]int, 
      Civl_VoteChannel: [vote]int, 
      Civl_votes: [int]vote, 
      Civl_decisions: [int]decision :: 
    true)
}

implementation MAIN4(pids: Set_230) returns (Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int)
{
  var dec: decision;
  var pids': Set_230;
  var participantPids: Set_230;

  /*** structured program:
    assert Init(pids->val, RequestChannel, VoteChannel, DecisionChannel, decisions);
    assume {:add_to_pool "INV4", 0} true;
    havoc RequestChannel, VoteChannel, votes;
    if (*)
    {
        dec := COMMIT();
    }
    else
    {
        dec := ABORT();
    }

    assume dec == COMMIT() ==> (forall i: int :: pid(i) ==> votes[i] == YES());
    decisions[0] := dec;
    DecisionChannel := (lambda i: int :: (lambda d: decision :: (if pid(i) && d == dec then 1 else 0)));
    pids' := pids;
    call participantPids := Set_Get_335(pids', (lambda i: int :: pid(i)));
    call {:linear participantPids} create_asyncs_4801((lambda pa: PARTICIPANT2 :: pid(pa->pid->val)));
  **** end structured program */

  anon0:
    Civl_PAs_PARTICIPANT2 := MapConst_3_14186(0);
    assume {:add_to_pool "INV4", 0} true;
    havoc RequestChannel, VoteChannel, votes;
    goto anon4_Then, anon4_Else;

  anon4_Else:
    dec := ABORT();
    goto anon3;

  anon3:
    assume dec == COMMIT() ==> (forall i: int :: pid(i) ==> votes[i] == YES());
    decisions[0] := dec;
    DecisionChannel := (lambda i: int :: (lambda d: decision :: (if pid(i) && d == dec then 1 else 0)));
    pids' := pids;
    participantPids := Set_230((lambda i: int :: pid(i)));
    pids' := Set_Difference_335(pids', participantPids);
    Civl_PAs_PARTICIPANT2 := MapAdd_14175(Civl_PAs_PARTICIPANT2, 
      MapIte_14193_3((lambda pa: PARTICIPANT2 :: pid(pa->pid->val)), 
        MapConst_3_14186(1), 
        MapConst_3_14186(0)));
    return;

  anon4_Then:
    dec := COMMIT();
    goto anon3;
}



procedure {:inline 1} MAIN4(pids: Set_230) returns (Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int);
  modifies RequestChannel, VoteChannel, DecisionChannel, votes, decisions;



function {:inline} Civl_InputOutputRelation_MAIN4(pids: Set_230, Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int) : bool
{
  (exists Civl_old_RequestChannel: [int]int, 
      Civl_old_DecisionChannel: [int][decision]int, 
      Civl_old_VoteChannel: [vote]int, 
      Civl_old_votes: [int]vote, 
      Civl_old_decisions: [int]decision, 
      Civl_RequestChannel: [int]int, 
      Civl_DecisionChannel: [int][decision]int, 
      Civl_VoteChannel: [vote]int, 
      Civl_votes: [int]vote, 
      Civl_decisions: [int]decision :: 
    (true
         ==> (forall votes: [int]vote :: 
          (COMMIT() == COMMIT()
             ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
             ==> (forall Civl_pa1: PARTICIPANT2, Civl_pa2: PARTICIPANT2 :: 
              (lambda pa: PARTICIPANT2 :: pid(pa->pid->val))[Civl_pa1]
                   && (lambda pa: PARTICIPANT2 :: pid(pa->pid->val))[Civl_pa2]
                   && Civl_pa1 != Civl_pa2
                 ==> Civl_pa1->pid != Civl_pa2->pid)))
       && (true
         ==> (forall votes: [int]vote :: 
          (COMMIT() == COMMIT()
             ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
             ==> (forall Civl_pa: PARTICIPANT2 :: 
              (lambda pa: PARTICIPANT2 :: pid(pa->pid->val))[Civl_pa]
                 ==> Set_Contains_43(Set_230((lambda i: int :: pid(i))), Civl_pa->pid->val))))
       && (true
         ==> (forall votes: [int]vote :: 
          (COMMIT() == COMMIT()
             ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
             ==> Set_IsSubset_335(Set_230((lambda i: int :: pid(i))), pids)))
       && (true
         ==> (forall votes: [int]vote :: 
          (ABORT() == COMMIT()
             ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
             ==> (forall Civl_pa1: PARTICIPANT2, Civl_pa2: PARTICIPANT2 :: 
              (lambda pa: PARTICIPANT2 :: pid(pa->pid->val))[Civl_pa1]
                   && (lambda pa: PARTICIPANT2 :: pid(pa->pid->val))[Civl_pa2]
                   && Civl_pa1 != Civl_pa2
                 ==> Civl_pa1->pid != Civl_pa2->pid)))
       && (true
         ==> (forall votes: [int]vote :: 
          (ABORT() == COMMIT()
             ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
             ==> (forall Civl_pa: PARTICIPANT2 :: 
              (lambda pa: PARTICIPANT2 :: pid(pa->pid->val))[Civl_pa]
                 ==> Set_Contains_43(Set_230((lambda i: int :: pid(i))), Civl_pa->pid->val))))
       && (true
         ==> (forall votes: [int]vote :: 
          (ABORT() == COMMIT()
             ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
             ==> Set_IsSubset_335(Set_230((lambda i: int :: pid(i))), pids)))
       && Init(pids->val, 
        Civl_old_RequestChannel, 
        Civl_old_VoteChannel, 
        Civl_old_DecisionChannel, 
        Civl_old_decisions)
       && ((
          true
           && (COMMIT() == COMMIT() ==> (forall i: int :: pid(i) ==> Civl_votes[i] == YES()))
           && Civl_decisions == Civl_old_decisions[0 := COMMIT()]
           && Civl_DecisionChannel
             == (lambda i: int :: 
              (lambda d: decision :: (if pid(i) && d == COMMIT() then 1 else 0)))
           && Civl_PAs_PARTICIPANT2
             == MapAdd_14175(MapConst_3_14186(0), 
              MapIte_14193_3((lambda pa: PARTICIPANT2 :: pid(pa->pid->val)), 
                MapConst_3_14186(1), 
                MapConst_3_14186(0))))
         || (
          true
           && (ABORT() == COMMIT() ==> (forall i: int :: pid(i) ==> Civl_votes[i] == YES()))
           && Civl_decisions == Civl_old_decisions[0 := ABORT()]
           && Civl_DecisionChannel
             == (lambda i: int :: 
              (lambda d: decision :: (if pid(i) && d == ABORT() then 1 else 0)))
           && Civl_PAs_PARTICIPANT2
             == MapAdd_14175(MapConst_3_14186(0), 
              MapIte_14193_3((lambda pa: PARTICIPANT2 :: pid(pa->pid->val)), 
                MapConst_3_14186(1), 
                MapConst_3_14186(0))))))
}

implementation MAIN3(pids: Set_230)
   returns (Civl_PAs_COORDINATOR2: [COORDINATOR2]int, 
    Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int)
{
  var pids': Set_230;
  var pid: One_43;
  var participantPids: Set_230;

  /*** structured program:
    assert Init(pids->val, RequestChannel, VoteChannel, DecisionChannel, decisions);
    havoc RequestChannel, VoteChannel, votes;
    assume VoteChannel[YES()] >= 0 && VoteChannel[NO()] >= 0;
    assume VoteChannel[YES()] + VoteChannel[NO()] <= n;
    assume VoteChannel[YES()] == n ==> (forall i: int :: pid(i) ==> votes[i] == YES());
    pids' := pids;
    call pid := One_Get_687(pids', 0);
    async call COORDINATOR2(pid);
    call participantPids := Set_Get_335(pids', (lambda i: int :: pid(i)));
    call {:linear participantPids} create_asyncs_4801((lambda pa: PARTICIPANT2 :: pid(pa->pid->val)));
  **** end structured program */

  anon0:
    Civl_PAs_COORDINATOR2, Civl_PAs_PARTICIPANT2 := MapConst_3_14244(0), MapConst_3_14186(0);
    havoc RequestChannel, VoteChannel, votes;
    assume VoteChannel[YES()] >= 0 && VoteChannel[NO()] >= 0;
    assume VoteChannel[YES()] + VoteChannel[NO()] <= n;
    assume VoteChannel[YES()] == n ==> (forall i: int :: pid(i) ==> votes[i] == YES());
    pids' := pids;
    pids' := Set_Remove_687(pids', 0);
    pid := One_43(0);
    Civl_PAs_COORDINATOR2 := MapAdd_14233(Civl_PAs_COORDINATOR2, MapConst_3_14244(0)[COORDINATOR2(pid) := 1]);
    participantPids := Set_230((lambda i: int :: pid(i)));
    pids' := Set_Difference_335(pids', participantPids);
    Civl_PAs_PARTICIPANT2 := MapAdd_14175(Civl_PAs_PARTICIPANT2, 
      MapIte_14193_3((lambda pa: PARTICIPANT2 :: pid(pa->pid->val)), 
        MapConst_3_14186(1), 
        MapConst_3_14186(0)));
    return;
}



procedure {:inline 1} MAIN3(pids: Set_230)
   returns (Civl_PAs_COORDINATOR2: [COORDINATOR2]int, 
    Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int);
  modifies RequestChannel, VoteChannel, votes;



function {:inline} Civl_InputOutputRelation_MAIN3(pids: Set_230, 
    Civl_PAs_COORDINATOR2: [COORDINATOR2]int, 
    Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int)
   : bool
{
  (exists Civl_old_RequestChannel: [int]int, 
      Civl_old_DecisionChannel: [int][decision]int, 
      Civl_old_VoteChannel: [vote]int, 
      Civl_old_votes: [int]vote, 
      Civl_old_decisions: [int]decision, 
      Civl_RequestChannel: [int]int, 
      Civl_DecisionChannel: [int][decision]int, 
      Civl_VoteChannel: [vote]int, 
      Civl_votes: [int]vote, 
      Civl_decisions: [int]decision :: 
    (forall VoteChannel: [vote]int, votes: [int]vote :: 
        VoteChannel[YES()] >= 0 && VoteChannel[NO()] >= 0
           ==> 
          VoteChannel[YES()] + VoteChannel[NO()] <= n
           ==> 
          (VoteChannel[YES()] == n
           ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
           ==> (forall Civl_pa1: PARTICIPANT2, Civl_pa2: PARTICIPANT2 :: 
            (lambda pa: PARTICIPANT2 :: pid(pa->pid->val))[Civl_pa1]
                 && (lambda pa: PARTICIPANT2 :: pid(pa->pid->val))[Civl_pa2]
                 && Civl_pa1 != Civl_pa2
               ==> Civl_pa1->pid != Civl_pa2->pid))
       && (forall VoteChannel: [vote]int, votes: [int]vote :: 
        VoteChannel[YES()] >= 0 && VoteChannel[NO()] >= 0
           ==> 
          VoteChannel[YES()] + VoteChannel[NO()] <= n
           ==> 
          (VoteChannel[YES()] == n
           ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
           ==> (forall Civl_pa: PARTICIPANT2 :: 
            (lambda pa: PARTICIPANT2 :: pid(pa->pid->val))[Civl_pa]
               ==> Set_Contains_43(Set_230((lambda i: int :: pid(i))), Civl_pa->pid->val)))
       && (forall VoteChannel: [vote]int, votes: [int]vote :: 
        VoteChannel[YES()] >= 0 && VoteChannel[NO()] >= 0
           ==> 
          VoteChannel[YES()] + VoteChannel[NO()] <= n
           ==> 
          (VoteChannel[YES()] == n
           ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
           ==> Set_IsSubset_335(Set_230((lambda i: int :: pid(i))), Set_Remove_687(pids, 0)))
       && (forall VoteChannel: [vote]int, votes: [int]vote :: 
        VoteChannel[YES()] >= 0 && VoteChannel[NO()] >= 0
           ==> 
          VoteChannel[YES()] + VoteChannel[NO()] <= n
           ==> 
          (VoteChannel[YES()] == n
           ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
           ==> Set_Contains_43(pids, 0))
       && Init(pids->val, 
        Civl_old_RequestChannel, 
        Civl_old_VoteChannel, 
        Civl_old_DecisionChannel, 
        Civl_old_decisions)
       && 
      Civl_VoteChannel[YES()] >= 0
       && Civl_VoteChannel[NO()] >= 0
       && Civl_VoteChannel[YES()] + Civl_VoteChannel[NO()] <= n
       && (Civl_VoteChannel[YES()] == n
         ==> (forall i: int :: pid(i) ==> Civl_votes[i] == YES()))
       && Civl_PAs_COORDINATOR2
         == MapAdd_14233(MapConst_3_14244(0), MapConst_3_14244(0)[COORDINATOR2(One_43(0)) := 1])
       && Civl_PAs_PARTICIPANT2
         == MapAdd_14175(MapConst_3_14186(0), 
          MapIte_14193_3((lambda pa: PARTICIPANT2 :: pid(pa->pid->val)), 
            MapConst_3_14186(1), 
            MapConst_3_14186(0))))
}

implementation MAIN2(pids: Set_230)
   returns (Civl_PAs_COORDINATOR2: [COORDINATOR2]int, 
    Civl_PAs_PARTICIPANT1: [PARTICIPANT1]int)
{
  var pids': Set_230;
  var pid: One_43;
  var participantPids: Set_230;

  /*** structured program:
    assert Init(pids->val, RequestChannel, VoteChannel, DecisionChannel, decisions);
    assume {:add_to_pool "INV2", 0} true;
    RequestChannel := (lambda i: int :: (if pid(i) then 1 else 0));
    pids' := pids;
    call pid := One_Get_687(pids', 0);
    async call COORDINATOR2(pid);
    call participantPids := Set_Get_335(pids', (lambda i: int :: pid(i)));
    call {:linear participantPids} create_asyncs_4825((lambda pa: PARTICIPANT1 :: pid(pa->pid->val)));
  **** end structured program */

  anon0:
    Civl_PAs_COORDINATOR2, Civl_PAs_PARTICIPANT1 := MapConst_3_14244(0), MapConst_3_14154(0);
    assume {:add_to_pool "INV2", 0} true;
    RequestChannel := (lambda i: int :: (if pid(i) then 1 else 0));
    pids' := pids;
    pids' := Set_Remove_687(pids', 0);
    pid := One_43(0);
    Civl_PAs_COORDINATOR2 := MapAdd_14233(Civl_PAs_COORDINATOR2, MapConst_3_14244(0)[COORDINATOR2(pid) := 1]);
    participantPids := Set_230((lambda i: int :: pid(i)));
    pids' := Set_Difference_335(pids', participantPids);
    Civl_PAs_PARTICIPANT1 := MapAdd_14143(Civl_PAs_PARTICIPANT1, 
      MapIte_14161_3((lambda pa: PARTICIPANT1 :: pid(pa->pid->val)), 
        MapConst_3_14154(1), 
        MapConst_3_14154(0)));
    return;
}



procedure {:inline 1} MAIN2(pids: Set_230)
   returns (Civl_PAs_COORDINATOR2: [COORDINATOR2]int, 
    Civl_PAs_PARTICIPANT1: [PARTICIPANT1]int);
  modifies RequestChannel;



function {:inline} Civl_InputOutputRelation_MAIN2(pids: Set_230, 
    Civl_PAs_COORDINATOR2: [COORDINATOR2]int, 
    Civl_PAs_PARTICIPANT1: [PARTICIPANT1]int)
   : bool
{
  (exists Civl_old_RequestChannel: [int]int, 
      Civl_old_DecisionChannel: [int][decision]int, 
      Civl_old_VoteChannel: [vote]int, 
      Civl_old_votes: [int]vote, 
      Civl_old_decisions: [int]decision, 
      Civl_RequestChannel: [int]int, 
      Civl_DecisionChannel: [int][decision]int, 
      Civl_VoteChannel: [vote]int, 
      Civl_votes: [int]vote, 
      Civl_decisions: [int]decision :: 
    (true
         ==> (forall Civl_pa1: PARTICIPANT1, Civl_pa2: PARTICIPANT1 :: 
          (lambda pa: PARTICIPANT1 :: pid(pa->pid->val))[Civl_pa1]
               && (lambda pa: PARTICIPANT1 :: pid(pa->pid->val))[Civl_pa2]
               && Civl_pa1 != Civl_pa2
             ==> Civl_pa1->pid != Civl_pa2->pid))
       && (true
         ==> (forall Civl_pa: PARTICIPANT1 :: 
          (lambda pa: PARTICIPANT1 :: pid(pa->pid->val))[Civl_pa]
             ==> Set_Contains_43(Set_230((lambda i: int :: pid(i))), Civl_pa->pid->val)))
       && (true
         ==> Set_IsSubset_335(Set_230((lambda i: int :: pid(i))), Set_Remove_687(pids, 0)))
       && (true ==> Set_Contains_43(pids, 0))
       && Init(pids->val, 
        Civl_old_RequestChannel, 
        Civl_old_VoteChannel, 
        Civl_old_DecisionChannel, 
        Civl_old_decisions)
       && 
      true
       && Civl_RequestChannel == (lambda i: int :: (if pid(i) then 1 else 0))
       && Civl_PAs_COORDINATOR2
         == MapAdd_14233(MapConst_3_14244(0), MapConst_3_14244(0)[COORDINATOR2(One_43(0)) := 1])
       && Civl_PAs_PARTICIPANT1
         == MapAdd_14143(MapConst_3_14154(0), 
          MapIte_14161_3((lambda pa: PARTICIPANT1 :: pid(pa->pid->val)), 
            MapConst_3_14154(1), 
            MapConst_3_14154(0))))
}

implementation MAIN1(pids: Set_230)
   returns (Civl_PAs_COORDINATOR1: [COORDINATOR1]int, 
    Civl_PAs_PARTICIPANT1: [PARTICIPANT1]int)
{
  var pids': Set_230;
  var pid: One_43;
  var participantPids: Set_230;

  /*** structured program:
    assert Init(pids->val, RequestChannel, VoteChannel, DecisionChannel, decisions);
    pids' := pids;
    call pid := One_Get_687(pids', 0);
    async call COORDINATOR1(pid);
    call participantPids := Set_Get_335(pids', (lambda i: int :: pid(i)));
    call {:linear participantPids} create_asyncs_4825((lambda pa: PARTICIPANT1 :: pid(pa->pid->val)));
  **** end structured program */

  anon0:
    Civl_PAs_COORDINATOR1, Civl_PAs_PARTICIPANT1 := MapConst_3_4754(0), MapConst_3_14154(0);
    pids' := pids;
    pids' := Set_Remove_687(pids', 0);
    pid := One_43(0);
    Civl_PAs_COORDINATOR1 := MapAdd_14207(Civl_PAs_COORDINATOR1, MapConst_3_4754(0)[COORDINATOR1(pid) := 1]);
    participantPids := Set_230((lambda i: int :: pid(i)));
    pids' := Set_Difference_335(pids', participantPids);
    Civl_PAs_PARTICIPANT1 := MapAdd_14143(Civl_PAs_PARTICIPANT1, 
      MapIte_14161_3((lambda pa: PARTICIPANT1 :: pid(pa->pid->val)), 
        MapConst_3_14154(1), 
        MapConst_3_14154(0)));
    return;
}



procedure {:inline 1} MAIN1(pids: Set_230)
   returns (Civl_PAs_COORDINATOR1: [COORDINATOR1]int, 
    Civl_PAs_PARTICIPANT1: [PARTICIPANT1]int);



function {:inline} Civl_InputOutputRelation_MAIN1(pids: Set_230, 
    Civl_PAs_COORDINATOR1: [COORDINATOR1]int, 
    Civl_PAs_PARTICIPANT1: [PARTICIPANT1]int)
   : bool
{
  (exists Civl_old_RequestChannel: [int]int, 
      Civl_old_DecisionChannel: [int][decision]int, 
      Civl_old_VoteChannel: [vote]int, 
      Civl_old_votes: [int]vote, 
      Civl_old_decisions: [int]decision, 
      Civl_RequestChannel: [int]int, 
      Civl_DecisionChannel: [int][decision]int, 
      Civl_VoteChannel: [vote]int, 
      Civl_votes: [int]vote, 
      Civl_decisions: [int]decision :: 
    (forall Civl_pa1: PARTICIPANT1, Civl_pa2: PARTICIPANT1 :: 
        (lambda pa: PARTICIPANT1 :: pid(pa->pid->val))[Civl_pa1]
             && (lambda pa: PARTICIPANT1 :: pid(pa->pid->val))[Civl_pa2]
             && Civl_pa1 != Civl_pa2
           ==> Civl_pa1->pid != Civl_pa2->pid)
       && (forall Civl_pa: PARTICIPANT1 :: 
        (lambda pa: PARTICIPANT1 :: pid(pa->pid->val))[Civl_pa]
           ==> Set_Contains_43(Set_230((lambda i: int :: pid(i))), Civl_pa->pid->val))
       && Set_IsSubset_335(Set_230((lambda i: int :: pid(i))), Set_Remove_687(pids, 0))
       && Set_Contains_43(pids, 0)
       && Init(pids->val, 
        Civl_old_RequestChannel, 
        Civl_old_VoteChannel, 
        Civl_old_DecisionChannel, 
        Civl_old_decisions)
       && 
      Civl_PAs_COORDINATOR1
         == MapAdd_14207(MapConst_3_4754(0), MapConst_3_4754(0)[COORDINATOR1(One_43(0)) := 1])
       && Civl_PAs_PARTICIPANT1
         == MapAdd_14143(MapConst_3_14154(0), 
          MapIte_14161_3((lambda pa: PARTICIPANT1 :: pid(pa->pid->val)), 
            MapConst_3_14154(1), 
            MapConst_3_14154(0))))
}

procedure Civl_main_1(pids: Set_230);
  requires Init(pids->val, RequestChannel, VoteChannel, DecisionChannel, decisions);
  modifies RequestChannel, DecisionChannel, VoteChannel, votes, decisions;



procedure Civl_participant1_1(pid: One_43);
  requires pid(pid->val);
  modifies RequestChannel, DecisionChannel, VoteChannel, votes, decisions;



procedure Civl_participant2_1(pid: One_43);
  requires pid(pid->val);
  modifies RequestChannel, DecisionChannel, VoteChannel, votes, decisions;



procedure Civl_coordinator1_1(pid: One_43);
  requires pid->val == 0;
  requires (forall vv: vote :: VoteChannel[vv] >= 0);
  modifies RequestChannel, DecisionChannel, VoteChannel, votes, decisions;



procedure Civl_coordinator2_1(pid: One_43);
  requires pid->val == 0;
  requires (forall vv: vote :: VoteChannel[vv] >= 0);
  modifies RequestChannel, DecisionChannel, VoteChannel, votes, decisions;



implementation Civl_main_1(pids: Set_230)
{
  var i: int;
  var Coordinator1_PAs: [COORDINATOR1]int;
  var Participant1_PAs: [PARTICIPANT1]int;
  var pid: One_43;
  var pids': Set_230;
  var Civl_global_old_RequestChannel: [int]int;
  var Civl_global_old_DecisionChannel: [int][decision]int;
  var Civl_global_old_VoteChannel: [vote]int;
  var Civl_global_old_votes: [int]vote;
  var Civl_global_old_decisions: [int]decision;
  var Civl_pc: bool;
  var Civl_ok: bool;
  var Civl_eval: bool;
  var Civl_old_Coordinator1_PAs: [COORDINATOR1]int;
  var Civl_old_Participant1_PAs: [PARTICIPANT1]int;
  var Civl_linear_int_available: [int]bool;

  /*** structured program:
    pids' := pids;
    call pid := One_Get_687(pids', 0);
    async call coordinator1(pid);
    i := 1;
    while (i <= n)
      invariant 1 <= i && i <= n + 1;
      invariant (forall ii: int :: pid(ii) && ii >= i ==> pids'->val[ii]);
      invariant Coordinator1_PAs == MapConst_3_4754(0)[COORDINATOR1(One_43(0)) := 1];
      invariant Participant1_PAs
         == (lambda pa: PARTICIPANT1 :: 
          (if pid(pa->pid->val) && pa->pid->val < i then 1 else 0));
    {
        call pid := One_Get(pids', i);
        async call participant1(pid);
        i := i + 1;
    }
  **** end structured program */

  Civl_init:
    havoc RequestChannel, DecisionChannel, VoteChannel, votes, decisions;
    assume Init(old(pids)->val, RequestChannel, VoteChannel, DecisionChannel, decisions);
    Civl_global_old_RequestChannel, Civl_global_old_DecisionChannel, Civl_global_old_VoteChannel, Civl_global_old_votes, Civl_global_old_decisions := RequestChannel, DecisionChannel, VoteChannel, votes, decisions;
    Civl_pc, Civl_ok, Civl_eval := false, false, false;
    Civl_old_Coordinator1_PAs, Civl_old_Participant1_PAs := Coordinator1_PAs, Participant1_PAs;
    assume (forall Civl_pa1: PARTICIPANT1, Civl_pa2: PARTICIPANT1 :: 
        (lambda pa: PARTICIPANT1 :: pid(pa->pid->val))[Civl_pa1]
             && (lambda pa: PARTICIPANT1 :: pid(pa->pid->val))[Civl_pa2]
             && Civl_pa1 != Civl_pa2
           ==> Civl_pa1->pid != Civl_pa2->pid)
       && (forall Civl_pa: PARTICIPANT1 :: 
        (lambda pa: PARTICIPANT1 :: pid(pa->pid->val))[Civl_pa]
           ==> Set_Contains_43(Set_230((lambda i: int :: pid(i))), Civl_pa->pid->val))
       && Set_IsSubset_335(Set_230((lambda i: int :: pid(i))), Set_Remove_687(pids, 0))
       && Set_Contains_43(pids, 0)
       && Init(pids->val, RequestChannel, VoteChannel, DecisionChannel, decisions);
    Civl_linear_int_available := MapOr_230(Set_Collector_230(pids), MapConst_5_150(false));
    goto anon0;

  anon0:
    assume Coordinator1_PAs == MapConst_3_4754(0)
       && Participant1_PAs == MapConst_3_14154(0);
    pids' := pids;
    assert Set_Contains_43(pids', 0);
    pids' := Set_Remove_687(pids', 0);
    pid := One_43(0);
    call Civl_AsyncCall_coordinator1_1(pid);
    Coordinator1_PAs := Coordinator1_PAs[COORDINATOR1(pid) := Coordinator1_PAs[COORDINATOR1(pid)] + 1];
    i := 1;
    goto anon2_LoopHead;

  anon2_LoopHead:
    assert 1 <= i && i <= n + 1;
    assert (forall ii: int :: pid(ii) && ii >= i ==> pids'->val[ii]);
    assert Coordinator1_PAs == MapConst_3_4754(0)[COORDINATOR1(One_43(0)) := 1];
    assert Participant1_PAs
       == (lambda pa: PARTICIPANT1 :: 
        (if pid(pa->pid->val) && pa->pid->val < i then 1 else 0));
    goto anon2_LoopDone, anon2_LoopBody;

  anon2_LoopBody:
    assume {:partition} i <= n;
    assert Set_Contains_43(pids', i);
    pids' := Set_Remove_687(pids', i);
    pid := One_43(i);
    call Civl_AsyncCall_participant1_1(pid);
    Participant1_PAs := Participant1_PAs[PARTICIPANT1(pid) := Participant1_PAs[PARTICIPANT1(pid)] + 1];
    i := i + 1;
    goto anon2_LoopHead;

  anon2_LoopDone:
    assume {:partition} n < i;
    goto Civl_ReturnChecker, Civl_UnifiedReturn, Civl_NoninterferenceChecker;

  Civl_NoninterferenceChecker:
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_int_available, Civl_global_old_RequestChannel, Civl_global_old_DecisionChannel, Civl_global_old_VoteChannel, Civl_global_old_votes, Civl_global_old_decisions);
    assume false;
    return;

  Civl_RefinementChecker:
    assert Civl_pc
       || 
      (
        RequestChannel == Civl_global_old_RequestChannel
         && DecisionChannel == Civl_global_old_DecisionChannel
         && VoteChannel == Civl_global_old_VoteChannel
         && votes == Civl_global_old_votes
         && decisions == Civl_global_old_decisions)
       || Civl_eval;
    assert Civl_pc
       ==> RequestChannel == Civl_global_old_RequestChannel
         && DecisionChannel == Civl_global_old_DecisionChannel
         && VoteChannel == Civl_global_old_VoteChannel
         && votes == Civl_global_old_votes
         && decisions == Civl_global_old_decisions
         && 
        Coordinator1_PAs == Civl_old_Coordinator1_PAs
         && Participant1_PAs == Civl_old_Participant1_PAs;
    assume false;
    return;

  Civl_UnchangedChecker:
    assert RequestChannel == Civl_global_old_RequestChannel
       && DecisionChannel == Civl_global_old_DecisionChannel
       && VoteChannel == Civl_global_old_VoteChannel
       && votes == Civl_global_old_votes
       && decisions == Civl_global_old_decisions;
    assert Civl_pc
       ==> Coordinator1_PAs == Civl_old_Coordinator1_PAs
         && Participant1_PAs == Civl_old_Participant1_PAs;
    assume false;
    return;

  Civl_ReturnChecker:
    Civl_eval := Coordinator1_PAs
         == MapAdd_14207(MapConst_3_4754(0), MapConst_3_4754(0)[COORDINATOR1(One_43(0)) := 1])
       && Participant1_PAs
         == MapAdd_14143(MapConst_3_14154(0), 
          MapIte_14161_3((lambda pa: PARTICIPANT1 :: pid(pa->pid->val)), 
            MapConst_3_14154(1), 
            MapConst_3_14154(0)))
       && RequestChannel == Civl_global_old_RequestChannel
       && DecisionChannel == Civl_global_old_DecisionChannel
       && VoteChannel == Civl_global_old_VoteChannel
       && votes == Civl_global_old_votes
       && decisions == Civl_global_old_decisions;
    assert Civl_pc
       || 
      (
        RequestChannel == Civl_global_old_RequestChannel
         && DecisionChannel == Civl_global_old_DecisionChannel
         && VoteChannel == Civl_global_old_VoteChannel
         && votes == Civl_global_old_votes
         && decisions == Civl_global_old_decisions)
       || Civl_eval;
    assert Civl_pc
       ==> RequestChannel == Civl_global_old_RequestChannel
         && DecisionChannel == Civl_global_old_DecisionChannel
         && VoteChannel == Civl_global_old_VoteChannel
         && votes == Civl_global_old_votes
         && decisions == Civl_global_old_decisions
         && 
        Coordinator1_PAs == Civl_old_Coordinator1_PAs
         && Participant1_PAs == Civl_old_Participant1_PAs;
    Civl_pc, Civl_ok := RequestChannel == Civl_global_old_RequestChannel
         && DecisionChannel == Civl_global_old_DecisionChannel
         && VoteChannel == Civl_global_old_VoteChannel
         && votes == Civl_global_old_votes
         && decisions == Civl_global_old_decisions
       ==> Civl_pc, Civl_eval
       || (
        Coordinator1_PAs == Civl_old_Coordinator1_PAs
         && Participant1_PAs == Civl_old_Participant1_PAs
         && Civl_ok);
    assert Civl_ok;
    assume false;
    return;

  Civl_UnifiedReturn:
    return;
}



implementation Civl_participant1_1(pid: One_43)
{
  var v: vote;
  var Civl_collectedPAs_PARTICIPANT2: [PARTICIPANT2]int;
  var Civl_global_old_RequestChannel: [int]int;
  var Civl_global_old_DecisionChannel: [int][decision]int;
  var Civl_global_old_VoteChannel: [vote]int;
  var Civl_global_old_votes: [int]vote;
  var Civl_global_old_decisions: [int]decision;
  var Civl_pc: bool;
  var Civl_ok: bool;
  var Civl_eval: bool;
  var Civl_old_Civl_collectedPAs_PARTICIPANT2: [PARTICIPANT2]int;
  var Civl_linear_int_available: [int]bool;

  /*** structured program:
    if (*)
    {
        call receive_req(pid->val);
        havoc v;
        call set_vote(pid, v);
        call send_vote(v);
    }

    async call participant2(pid);
  **** end structured program */

  Civl_init:
    havoc RequestChannel, DecisionChannel, VoteChannel, votes, decisions;
    assume pid(pid->val);
    Civl_global_old_RequestChannel, Civl_global_old_DecisionChannel, Civl_global_old_VoteChannel, Civl_global_old_votes, Civl_global_old_decisions := RequestChannel, DecisionChannel, VoteChannel, votes, decisions;
    Civl_pc, Civl_ok, Civl_eval := false, false, false;
    Civl_old_Civl_collectedPAs_PARTICIPANT2 := Civl_collectedPAs_PARTICIPANT2;
    assume pid(pid->val);
    Civl_linear_int_available := MapOr_230(One_Collector_43(pid), MapConst_5_150(false));
    goto anon0;

  anon0:
    assume Civl_collectedPAs_PARTICIPANT2 == MapConst_3_14186(0);
    goto anon3_Then, anon3_Else;

  anon3_Else:
    goto anon2;

  anon2:
    call Civl_AsyncCall_participant2_1(pid);
    Civl_collectedPAs_PARTICIPANT2 := Civl_collectedPAs_PARTICIPANT2[PARTICIPANT2(pid) := Civl_collectedPAs_PARTICIPANT2[PARTICIPANT2(pid)] + 1];
    goto Civl_ReturnChecker, Civl_UnifiedReturn, Civl_NoninterferenceChecker;

  anon3_Then:
    call RECEIVE_REQ(pid->val);
    havoc v;
    call SET_VOTE(pid, v);
    call SEND_VOTE(v);
    goto anon2;

  Civl_NoninterferenceChecker:
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_int_available, Civl_global_old_RequestChannel, Civl_global_old_DecisionChannel, Civl_global_old_VoteChannel, Civl_global_old_votes, Civl_global_old_decisions);
    assume false;
    return;

  Civl_RefinementChecker:
    assert Civl_pc
       || 
      (
        RequestChannel == Civl_global_old_RequestChannel
         && DecisionChannel == Civl_global_old_DecisionChannel
         && VoteChannel == Civl_global_old_VoteChannel
         && votes == Civl_global_old_votes
         && decisions == Civl_global_old_decisions)
       || Civl_eval;
    assert Civl_pc
       ==> RequestChannel == Civl_global_old_RequestChannel
         && DecisionChannel == Civl_global_old_DecisionChannel
         && VoteChannel == Civl_global_old_VoteChannel
         && votes == Civl_global_old_votes
         && decisions == Civl_global_old_decisions
         && Civl_collectedPAs_PARTICIPANT2 == Civl_old_Civl_collectedPAs_PARTICIPANT2;
    assume false;
    return;

  Civl_UnchangedChecker:
    assert RequestChannel == Civl_global_old_RequestChannel
       && DecisionChannel == Civl_global_old_DecisionChannel
       && VoteChannel == Civl_global_old_VoteChannel
       && votes == Civl_global_old_votes
       && decisions == Civl_global_old_decisions;
    assert Civl_pc
       ==> Civl_collectedPAs_PARTICIPANT2 == Civl_old_Civl_collectedPAs_PARTICIPANT2;
    assume false;
    return;

  Civl_ReturnChecker:
    Civl_eval := (
        Civl_global_old_RequestChannel[pid->val] > 0
         && RequestChannel
           == Civl_global_old_RequestChannel[pid->val := Civl_global_old_RequestChannel[pid->val] - 1]
         && votes == Civl_global_old_votes[pid->val := YES()]
         && VoteChannel
           == Civl_global_old_VoteChannel[YES() := Civl_global_old_VoteChannel[YES()] + 1]
         && Civl_collectedPAs_PARTICIPANT2
           == MapAdd_14175(MapConst_3_14186(0), MapConst_3_14186(0)[PARTICIPANT2(pid) := 1])
         && DecisionChannel == Civl_global_old_DecisionChannel
         && decisions == Civl_global_old_decisions)
       || (
        Civl_global_old_RequestChannel[pid->val] > 0
         && RequestChannel
           == Civl_global_old_RequestChannel[pid->val := Civl_global_old_RequestChannel[pid->val] - 1]
         && votes == Civl_global_old_votes[pid->val := NO()]
         && VoteChannel
           == Civl_global_old_VoteChannel[NO() := Civl_global_old_VoteChannel[NO()] + 1]
         && Civl_collectedPAs_PARTICIPANT2
           == MapAdd_14175(MapConst_3_14186(0), MapConst_3_14186(0)[PARTICIPANT2(pid) := 1])
         && DecisionChannel == Civl_global_old_DecisionChannel
         && decisions == Civl_global_old_decisions)
       || (
        Civl_collectedPAs_PARTICIPANT2
           == MapAdd_14175(MapConst_3_14186(0), MapConst_3_14186(0)[PARTICIPANT2(pid) := 1])
         && RequestChannel == Civl_global_old_RequestChannel
         && DecisionChannel == Civl_global_old_DecisionChannel
         && VoteChannel == Civl_global_old_VoteChannel
         && votes == Civl_global_old_votes
         && decisions == Civl_global_old_decisions);
    assert Civl_pc
       || 
      (
        RequestChannel == Civl_global_old_RequestChannel
         && DecisionChannel == Civl_global_old_DecisionChannel
         && VoteChannel == Civl_global_old_VoteChannel
         && votes == Civl_global_old_votes
         && decisions == Civl_global_old_decisions)
       || Civl_eval;
    assert Civl_pc
       ==> RequestChannel == Civl_global_old_RequestChannel
         && DecisionChannel == Civl_global_old_DecisionChannel
         && VoteChannel == Civl_global_old_VoteChannel
         && votes == Civl_global_old_votes
         && decisions == Civl_global_old_decisions
         && Civl_collectedPAs_PARTICIPANT2 == Civl_old_Civl_collectedPAs_PARTICIPANT2;
    Civl_pc, Civl_ok := RequestChannel == Civl_global_old_RequestChannel
         && DecisionChannel == Civl_global_old_DecisionChannel
         && VoteChannel == Civl_global_old_VoteChannel
         && votes == Civl_global_old_votes
         && decisions == Civl_global_old_decisions
       ==> Civl_pc, Civl_eval
       || (Civl_collectedPAs_PARTICIPANT2 == Civl_old_Civl_collectedPAs_PARTICIPANT2
         && Civl_ok);
    assert Civl_ok;
    assume false;
    return;

  Civl_UnifiedReturn:
    return;
}



implementation Civl_participant2_1(pid: One_43)
{
  var d: decision;
  var Civl_global_old_RequestChannel: [int]int;
  var Civl_global_old_DecisionChannel: [int][decision]int;
  var Civl_global_old_VoteChannel: [vote]int;
  var Civl_global_old_votes: [int]vote;
  var Civl_global_old_decisions: [int]decision;
  var Civl_pc: bool;
  var Civl_ok: bool;
  var Civl_eval: bool;
  var Civl_linear_int_available: [int]bool;

  /*** structured program:
    call d := receive_decision(pid->val);
    call set_decision(pid, d);
  **** end structured program */

  Civl_init:
    havoc RequestChannel, DecisionChannel, VoteChannel, votes, decisions;
    assume pid(pid->val);
    Civl_global_old_RequestChannel, Civl_global_old_DecisionChannel, Civl_global_old_VoteChannel, Civl_global_old_votes, Civl_global_old_decisions := RequestChannel, DecisionChannel, VoteChannel, votes, decisions;
    Civl_pc, Civl_ok, Civl_eval := false, false, false;
    assume DecisionChannel[pid->val][NONE()] == 0 && pid(pid->val);
    Civl_linear_int_available := MapOr_230(One_Collector_43(pid), MapConst_5_150(false));
    goto anon0;

  anon0:
    call d := RECEIVE_DECISION(pid->val);
    call SET_DECISION(pid, d);
    goto Civl_ReturnChecker, Civl_UnifiedReturn, Civl_NoninterferenceChecker;

  Civl_NoninterferenceChecker:
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_int_available, Civl_global_old_RequestChannel, Civl_global_old_DecisionChannel, Civl_global_old_VoteChannel, Civl_global_old_votes, Civl_global_old_decisions);
    assume false;
    return;

  Civl_RefinementChecker:
    assert Civl_pc
       || 
      (
        RequestChannel == Civl_global_old_RequestChannel
         && DecisionChannel == Civl_global_old_DecisionChannel
         && VoteChannel == Civl_global_old_VoteChannel
         && votes == Civl_global_old_votes
         && decisions == Civl_global_old_decisions)
       || Civl_eval;
    assert Civl_pc
       ==> RequestChannel == Civl_global_old_RequestChannel
         && DecisionChannel == Civl_global_old_DecisionChannel
         && VoteChannel == Civl_global_old_VoteChannel
         && votes == Civl_global_old_votes
         && decisions == Civl_global_old_decisions;
    assume false;
    return;

  Civl_UnchangedChecker:
    assert RequestChannel == Civl_global_old_RequestChannel
       && DecisionChannel == Civl_global_old_DecisionChannel
       && VoteChannel == Civl_global_old_VoteChannel
       && votes == Civl_global_old_votes
       && decisions == Civl_global_old_decisions;
    assert Civl_pc ==> true;
    assume false;
    return;

  Civl_ReturnChecker:
    Civl_eval := (
        Civl_global_old_DecisionChannel[pid->val][COMMIT()] > 0
         && DecisionChannel
           == Civl_global_old_DecisionChannel[pid->val := Civl_global_old_DecisionChannel[pid->val][COMMIT() := Civl_global_old_DecisionChannel[pid->val][COMMIT()] - 1]]
         && decisions == Civl_global_old_decisions[pid->val := COMMIT()]
         && RequestChannel == Civl_global_old_RequestChannel
         && VoteChannel == Civl_global_old_VoteChannel
         && votes == Civl_global_old_votes)
       || (
        Civl_global_old_DecisionChannel[pid->val][ABORT()] > 0
         && DecisionChannel
           == Civl_global_old_DecisionChannel[pid->val := Civl_global_old_DecisionChannel[pid->val][ABORT() := Civl_global_old_DecisionChannel[pid->val][ABORT()] - 1]]
         && decisions == Civl_global_old_decisions[pid->val := ABORT()]
         && RequestChannel == Civl_global_old_RequestChannel
         && VoteChannel == Civl_global_old_VoteChannel
         && votes == Civl_global_old_votes);
    assert Civl_pc
       || 
      (
        RequestChannel == Civl_global_old_RequestChannel
         && DecisionChannel == Civl_global_old_DecisionChannel
         && VoteChannel == Civl_global_old_VoteChannel
         && votes == Civl_global_old_votes
         && decisions == Civl_global_old_decisions)
       || Civl_eval;
    assert Civl_pc
       ==> RequestChannel == Civl_global_old_RequestChannel
         && DecisionChannel == Civl_global_old_DecisionChannel
         && VoteChannel == Civl_global_old_VoteChannel
         && votes == Civl_global_old_votes
         && decisions == Civl_global_old_decisions;
    Civl_pc, Civl_ok := RequestChannel == Civl_global_old_RequestChannel
         && DecisionChannel == Civl_global_old_DecisionChannel
         && VoteChannel == Civl_global_old_VoteChannel
         && votes == Civl_global_old_votes
         && decisions == Civl_global_old_decisions
       ==> Civl_pc, Civl_eval || Civl_ok;
    assert Civl_ok;
    assume false;
    return;

  Civl_UnifiedReturn:
    return;
}



implementation Civl_coordinator1_1(pid: One_43)
{
  var i: int;
  var old_RequestChannel: [int]int;
  var Civl_collectedPAs_COORDINATOR2: [COORDINATOR2]int;
  var Civl_global_old_RequestChannel: [int]int;
  var Civl_global_old_DecisionChannel: [int][decision]int;
  var Civl_global_old_VoteChannel: [vote]int;
  var Civl_global_old_votes: [int]vote;
  var Civl_global_old_decisions: [int]decision;
  var Civl_pc: bool;
  var Civl_ok: bool;
  var Civl_eval: bool;
  var Civl_old_Civl_collectedPAs_COORDINATOR2: [COORDINATOR2]int;
  var Civl_linear_int_available: [int]bool;

  /*** structured program:
    call {:layer 1} old_RequestChannel := Copy_9661(RequestChannel);
    i := 1;
    while (i <= n)
      invariant 1 <= i && i <= n + 1;
      invariant RequestChannel
         == (lambda ii: int :: 
          (if pid(ii) && ii < i
             then old_RequestChannel[ii] + 1
             else old_RequestChannel[ii]));
    {
        call send_request(i);
        i := i + 1;
    }

    async call coordinator2(pid);
  **** end structured program */

  Civl_init:
    havoc RequestChannel, DecisionChannel, VoteChannel, votes, decisions;
    assume pid->val == 0;
    assume (forall vv: vote :: VoteChannel[vv] >= 0);
    Civl_global_old_RequestChannel, Civl_global_old_DecisionChannel, Civl_global_old_VoteChannel, Civl_global_old_votes, Civl_global_old_decisions := RequestChannel, DecisionChannel, VoteChannel, votes, decisions;
    Civl_pc, Civl_ok, Civl_eval := false, false, false;
    Civl_old_Civl_collectedPAs_COORDINATOR2 := Civl_collectedPAs_COORDINATOR2;
    assume pid->val == 0;
    Civl_linear_int_available := MapOr_230(One_Collector_43(pid), MapConst_5_150(false));
    goto anon0;

  anon0:
    assume Civl_collectedPAs_COORDINATOR2 == MapConst_3_14244(0);
    call {:layer 1} old_RequestChannel := Copy_9661(RequestChannel);
    i := 1;
    goto anon3_LoopHead;

  anon3_LoopHead:
    assert 1 <= i && i <= n + 1;
    assert RequestChannel
       == (lambda ii: int :: 
        (if pid(ii) && ii < i
           then old_RequestChannel[ii] + 1
           else old_RequestChannel[ii]));
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    assume {:partition} i <= n;
    call SEND_REQUEST(i);
    i := i + 1;
    goto anon3_LoopHead;

  anon3_LoopDone:
    assume {:partition} n < i;
    goto anon2;

  anon2:
    call Civl_AsyncCall_coordinator2_1(pid);
    Civl_collectedPAs_COORDINATOR2 := Civl_collectedPAs_COORDINATOR2[COORDINATOR2(pid) := Civl_collectedPAs_COORDINATOR2[COORDINATOR2(pid)] + 1];
    goto Civl_ReturnChecker, Civl_UnifiedReturn, Civl_NoninterferenceChecker;

  Civl_NoninterferenceChecker:
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_int_available, Civl_global_old_RequestChannel, Civl_global_old_DecisionChannel, Civl_global_old_VoteChannel, Civl_global_old_votes, Civl_global_old_decisions);
    assume false;
    return;

  Civl_RefinementChecker:
    assert Civl_pc
       || 
      (
        RequestChannel == Civl_global_old_RequestChannel
         && DecisionChannel == Civl_global_old_DecisionChannel
         && VoteChannel == Civl_global_old_VoteChannel
         && votes == Civl_global_old_votes
         && decisions == Civl_global_old_decisions)
       || Civl_eval;
    assert Civl_pc
       ==> RequestChannel == Civl_global_old_RequestChannel
         && DecisionChannel == Civl_global_old_DecisionChannel
         && VoteChannel == Civl_global_old_VoteChannel
         && votes == Civl_global_old_votes
         && decisions == Civl_global_old_decisions
         && Civl_collectedPAs_COORDINATOR2 == Civl_old_Civl_collectedPAs_COORDINATOR2;
    assume false;
    return;

  Civl_UnchangedChecker:
    assert RequestChannel == Civl_global_old_RequestChannel
       && DecisionChannel == Civl_global_old_DecisionChannel
       && VoteChannel == Civl_global_old_VoteChannel
       && votes == Civl_global_old_votes
       && decisions == Civl_global_old_decisions;
    assert Civl_pc
       ==> Civl_collectedPAs_COORDINATOR2 == Civl_old_Civl_collectedPAs_COORDINATOR2;
    assume false;
    return;

  Civl_ReturnChecker:
    Civl_eval := RequestChannel
         == (lambda i: int :: 
          (if pid(i)
             then Civl_global_old_RequestChannel[i] + 1
             else Civl_global_old_RequestChannel[i]))
       && Civl_collectedPAs_COORDINATOR2
         == MapAdd_14233(MapConst_3_14244(0), MapConst_3_14244(0)[COORDINATOR2(pid) := 1])
       && DecisionChannel == Civl_global_old_DecisionChannel
       && VoteChannel == Civl_global_old_VoteChannel
       && votes == Civl_global_old_votes
       && decisions == Civl_global_old_decisions;
    assert Civl_pc
       || 
      (
        RequestChannel == Civl_global_old_RequestChannel
         && DecisionChannel == Civl_global_old_DecisionChannel
         && VoteChannel == Civl_global_old_VoteChannel
         && votes == Civl_global_old_votes
         && decisions == Civl_global_old_decisions)
       || Civl_eval;
    assert Civl_pc
       ==> RequestChannel == Civl_global_old_RequestChannel
         && DecisionChannel == Civl_global_old_DecisionChannel
         && VoteChannel == Civl_global_old_VoteChannel
         && votes == Civl_global_old_votes
         && decisions == Civl_global_old_decisions
         && Civl_collectedPAs_COORDINATOR2 == Civl_old_Civl_collectedPAs_COORDINATOR2;
    Civl_pc, Civl_ok := RequestChannel == Civl_global_old_RequestChannel
         && DecisionChannel == Civl_global_old_DecisionChannel
         && VoteChannel == Civl_global_old_VoteChannel
         && votes == Civl_global_old_votes
         && decisions == Civl_global_old_decisions
       ==> Civl_pc, Civl_eval
       || (Civl_collectedPAs_COORDINATOR2 == Civl_old_Civl_collectedPAs_COORDINATOR2
         && Civl_ok);
    assert Civl_ok;
    assume false;
    return;

  Civl_UnifiedReturn:
    return;
}



implementation Civl_coordinator2_1(pid: One_43)
{
  var d: decision;
  var v: vote;
  var i: int;
  var old_VoteChannel: [vote]int;
  var old_DecisionChannel: [int][decision]int;
  var Civl_global_old_RequestChannel: [int]int;
  var Civl_global_old_DecisionChannel: [int][decision]int;
  var Civl_global_old_VoteChannel: [vote]int;
  var Civl_global_old_votes: [int]vote;
  var Civl_global_old_decisions: [int]decision;
  var Civl_pc: bool;
  var Civl_ok: bool;
  var Civl_eval: bool;
  var Civl_linear_int_available: [int]bool;

  /*** structured program:
    call {:layer 1} old_VoteChannel := Copy_9822(VoteChannel);
    call {:layer 1} old_DecisionChannel := Copy_9869(DecisionChannel);
    i := 0;
    d := COMMIT();
    while (i < n)
      invariant 0 <= i && i <= n;
      invariant VoteChannel[YES()] == old_VoteChannel[YES()] - i;
      invariant old_VoteChannel[YES()] - i >= 0;
      invariant VoteChannel[NO()] == old_VoteChannel[NO()];
    {
        call v := receive_vote();
        if (v == NO())
        {
            d := ABORT();
            break;
        }

        i := i + 1;
    }

    call set_decision(pid, d);
    i := 1;
    while (i <= n)
      invariant 1 <= i && i <= n + 1;
      invariant DecisionChannel
         == (lambda ii: int :: 
          (lambda dd: decision :: 
            (if pid(ii) && ii < i && dd == d
               then old_DecisionChannel[ii][dd] + 1
               else old_DecisionChannel[ii][dd])));
    {
        call send_decision(i, d);
        i := i + 1;
    }
  **** end structured program */

  Civl_init:
    havoc RequestChannel, DecisionChannel, VoteChannel, votes, decisions;
    assume pid->val == 0;
    assume (forall vv: vote :: VoteChannel[vv] >= 0);
    Civl_global_old_RequestChannel, Civl_global_old_DecisionChannel, Civl_global_old_VoteChannel, Civl_global_old_votes, Civl_global_old_decisions := RequestChannel, DecisionChannel, VoteChannel, votes, decisions;
    Civl_pc, Civl_ok, Civl_eval := false, false, false;
    assume pid->val == 0;
    Civl_linear_int_available := MapOr_230(One_Collector_43(pid), MapConst_5_150(false));
    goto anon0;

  anon0:
    call {:layer 1} old_VoteChannel := Copy_9822(VoteChannel);
    call {:layer 1} old_DecisionChannel := Copy_9869(DecisionChannel);
    i := 0;
    d := COMMIT();
    goto anon6_LoopHead;

  anon6_LoopHead:
    assert 0 <= i && i <= n;
    assert VoteChannel[YES()] == old_VoteChannel[YES()] - i;
    assert old_VoteChannel[YES()] - i >= 0;
    assert VoteChannel[NO()] == old_VoteChannel[NO()];
    goto anon6_LoopDone, anon6_LoopBody;

  anon6_LoopBody:
    assume {:partition} i < n;
    call v := RECEIVE_VOTE();
    goto anon7_Then, anon7_Else;

  anon7_Else:
    assume {:partition} v != NO();
    goto anon3;

  anon3:
    i := i + 1;
    goto anon6_LoopHead;

  anon7_Then:
    assume {:partition} v == NO();
    d := ABORT();
    goto anon4;

  anon4:
    call SET_DECISION(pid, d);
    i := 1;
    goto anon8_LoopHead;

  anon8_LoopHead:
    assert 1 <= i && i <= n + 1;
    assert DecisionChannel
       == (lambda ii: int :: 
        (lambda dd: decision :: 
          (if pid(ii) && ii < i && dd == d
             then old_DecisionChannel[ii][dd] + 1
             else old_DecisionChannel[ii][dd])));
    goto anon8_LoopDone, anon8_LoopBody;

  anon8_LoopBody:
    assume {:partition} i <= n;
    call SEND_DECISION(i, d);
    i := i + 1;
    goto anon8_LoopHead;

  anon8_LoopDone:
    assume {:partition} n < i;
    goto Civl_ReturnChecker, Civl_UnifiedReturn, Civl_NoninterferenceChecker;

  anon6_LoopDone:
    assume {:partition} n <= i;
    goto anon4;

  Civl_NoninterferenceChecker:
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_int_available, Civl_global_old_RequestChannel, Civl_global_old_DecisionChannel, Civl_global_old_VoteChannel, Civl_global_old_votes, Civl_global_old_decisions);
    assume false;
    return;

  Civl_RefinementChecker:
    assert Civl_pc
       || 
      (
        RequestChannel == Civl_global_old_RequestChannel
         && DecisionChannel == Civl_global_old_DecisionChannel
         && VoteChannel == Civl_global_old_VoteChannel
         && votes == Civl_global_old_votes
         && decisions == Civl_global_old_decisions)
       || Civl_eval;
    assert Civl_pc
       ==> RequestChannel == Civl_global_old_RequestChannel
         && DecisionChannel == Civl_global_old_DecisionChannel
         && VoteChannel == Civl_global_old_VoteChannel
         && votes == Civl_global_old_votes
         && decisions == Civl_global_old_decisions;
    assume false;
    return;

  Civl_UnchangedChecker:
    assert RequestChannel == Civl_global_old_RequestChannel
       && DecisionChannel == Civl_global_old_DecisionChannel
       && VoteChannel == Civl_global_old_VoteChannel
       && votes == Civl_global_old_votes
       && decisions == Civl_global_old_decisions;
    assert Civl_pc ==> true;
    assume false;
    return;

  Civl_ReturnChecker:
    Civl_eval := (
        Civl_global_old_VoteChannel[YES()] >= n
         && decisions == Civl_global_old_decisions[pid->val := COMMIT()]
         && DecisionChannel
           == (lambda i: int :: 
            (lambda d: decision :: 
              (if pid(i) && d == COMMIT()
                 then Civl_global_old_DecisionChannel[i][d] + 1
                 else Civl_global_old_DecisionChannel[i][d])))
         && RequestChannel == Civl_global_old_RequestChannel
         && votes == Civl_global_old_votes)
       || (
        decisions == Civl_global_old_decisions[pid->val := ABORT()]
         && DecisionChannel
           == (lambda i: int :: 
            (lambda d: decision :: 
              (if pid(i) && d == ABORT()
                 then Civl_global_old_DecisionChannel[i][d] + 1
                 else Civl_global_old_DecisionChannel[i][d])))
         && RequestChannel == Civl_global_old_RequestChannel
         && votes == Civl_global_old_votes);
    assert Civl_pc
       || 
      (
        RequestChannel == Civl_global_old_RequestChannel
         && DecisionChannel == Civl_global_old_DecisionChannel
         && VoteChannel == Civl_global_old_VoteChannel
         && votes == Civl_global_old_votes
         && decisions == Civl_global_old_decisions)
       || Civl_eval;
    assert Civl_pc
       ==> RequestChannel == Civl_global_old_RequestChannel
         && DecisionChannel == Civl_global_old_DecisionChannel
         && VoteChannel == Civl_global_old_VoteChannel
         && votes == Civl_global_old_votes
         && decisions == Civl_global_old_decisions;
    Civl_pc, Civl_ok := RequestChannel == Civl_global_old_RequestChannel
         && DecisionChannel == Civl_global_old_DecisionChannel
         && VoteChannel == Civl_global_old_VoteChannel
         && votes == Civl_global_old_votes
         && decisions == Civl_global_old_decisions
       ==> Civl_pc, Civl_eval || Civl_ok;
    assert Civl_ok;
    assume false;
    return;

  Civl_UnifiedReturn:
    return;
}



procedure Civl_AsyncCall_coordinator1_1(pid: One_43);
  requires pid->val == 0;
  requires (forall vv: vote :: VoteChannel[vv] >= 0);



procedure Civl_AsyncCall_participant1_1(pid: One_43);
  requires pid(pid->val);



procedure Civl_AsyncCall_participant2_1(pid: One_43);
  requires pid(pid->val);



procedure Civl_AsyncCall_coordinator2_1(pid: One_43);
  requires pid->val == 0;
  requires (forall vv: vote :: VoteChannel[vv] >= 0);



procedure {:inline 1} Civl_NoninterferenceChecker_yield_YieldInit(Civl_linear_int_in: [int]bool, 
    Civl_snapshot_RequestChannel: [int]int, 
    Civl_snapshot_DecisionChannel: [int][decision]int, 
    Civl_snapshot_VoteChannel: [vote]int, 
    Civl_snapshot_votes: [int]vote, 
    Civl_snapshot_decisions: [int]decision);



implementation Civl_NoninterferenceChecker_yield_YieldInit(Civl_linear_int_in: [int]bool, 
    Civl_snapshot_RequestChannel: [int]int, 
    Civl_snapshot_DecisionChannel: [int][decision]int, 
    Civl_snapshot_VoteChannel: [vote]int, 
    Civl_snapshot_votes: [int]vote, 
    Civl_snapshot_decisions: [int]decision)
{
  var pids: Set_230;

  enter:
    goto exit, L;

  exit:
    return;

  L:
    assume (exists Civl_partition_int: [int]int :: 
      MapImp_230(Set_Collector_230(pids), MapEq_230_3(Civl_partition_int, MapConst_2959_2942(0)))
           == MapConst_5_150(true)
         && MapImp_230(Civl_linear_int_in, MapEq_230_3(Civl_partition_int, MapConst_2959_2942(1)))
           == MapConst_5_150(true));
    assume Init(pids->val, 
      Civl_snapshot_RequestChannel, 
      Civl_snapshot_VoteChannel, 
      Civl_snapshot_DecisionChannel, 
      Civl_snapshot_decisions);
    assert Init(pids->val, RequestChannel, VoteChannel, DecisionChannel, decisions);
    assume false;
    return;
}



procedure {:inline 1} Civl_NoninterferenceChecker_yield_YieldCoordinator(Civl_linear_int_in: [int]bool, 
    Civl_snapshot_RequestChannel: [int]int, 
    Civl_snapshot_DecisionChannel: [int][decision]int, 
    Civl_snapshot_VoteChannel: [vote]int, 
    Civl_snapshot_votes: [int]vote, 
    Civl_snapshot_decisions: [int]decision);



implementation Civl_NoninterferenceChecker_yield_YieldCoordinator(Civl_linear_int_in: [int]bool, 
    Civl_snapshot_RequestChannel: [int]int, 
    Civl_snapshot_DecisionChannel: [int][decision]int, 
    Civl_snapshot_VoteChannel: [vote]int, 
    Civl_snapshot_votes: [int]vote, 
    Civl_snapshot_decisions: [int]decision)
{

  enter:
    goto exit, L;

  exit:
    return;

  L:
    assume (forall vv: vote :: Civl_snapshot_VoteChannel[vv] >= 0);
    assert (forall vv: vote :: VoteChannel[vv] >= 0);
    assume false;
    return;
}



procedure {:inline 1} Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_int_in: [int]bool, 
    Civl_global_old_RequestChannel: [int]int, 
    Civl_global_old_DecisionChannel: [int][decision]int, 
    Civl_global_old_VoteChannel: [vote]int, 
    Civl_global_old_votes: [int]vote, 
    Civl_global_old_decisions: [int]decision);



implementation Civl_Wrapper_NoninterferenceChecker_1(Civl_Civl_linear_int_in: [int]bool, 
    Civl_Civl_global_old_RequestChannel: [int]int, 
    Civl_Civl_global_old_DecisionChannel: [int][decision]int, 
    Civl_Civl_global_old_VoteChannel: [vote]int, 
    Civl_Civl_global_old_votes: [int]vote, 
    Civl_Civl_global_old_decisions: [int]decision)
{

  enter:
    goto L_0, L_1;

  L_0:
    call Civl_NoninterferenceChecker_yield_YieldInit(Civl_Civl_linear_int_in, Civl_Civl_global_old_RequestChannel, Civl_Civl_global_old_DecisionChannel, Civl_Civl_global_old_VoteChannel, Civl_Civl_global_old_votes, Civl_Civl_global_old_decisions);
    return;

  L_1:
    call Civl_NoninterferenceChecker_yield_YieldCoordinator(Civl_Civl_linear_int_in, Civl_Civl_global_old_RequestChannel, Civl_Civl_global_old_DecisionChannel, Civl_Civl_global_old_VoteChannel, Civl_Civl_global_old_votes, Civl_Civl_global_old_decisions);
    return;
}



procedure Civl_PendingAsyncNoninterferenceChecker_PARTICIPANT1_2(pid: One_43) returns (Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int);
  requires pid(pid->val);
  modifies RequestChannel, DecisionChannel, VoteChannel, votes, decisions;



implementation Civl_PendingAsyncNoninterferenceChecker_PARTICIPANT1_2(pid: One_43) returns (Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int)
{
  var Civl_global_old_RequestChannel: [int]int;
  var Civl_global_old_DecisionChannel: [int][decision]int;
  var Civl_global_old_VoteChannel: [vote]int;
  var Civl_global_old_votes: [int]vote;
  var Civl_global_old_decisions: [int]decision;
  var Civl_linear_int_available: [int]bool;

  init:
    Civl_global_old_RequestChannel, Civl_global_old_DecisionChannel, Civl_global_old_VoteChannel, Civl_global_old_votes, Civl_global_old_decisions := RequestChannel, DecisionChannel, VoteChannel, votes, decisions;
    Civl_linear_int_available := MapOr_230(One_Collector_43(pid), MapConst_5_150(false));
    call Civl_PAs_PARTICIPANT2 := PARTICIPANT1(pid);
    call Civl_Wrapper_NoninterferenceChecker_2(Civl_linear_int_available, Civl_global_old_RequestChannel, Civl_global_old_DecisionChannel, Civl_global_old_VoteChannel, Civl_global_old_votes, Civl_global_old_decisions);
    return;
}



procedure Civl_PendingAsyncNoninterferenceChecker_PARTICIPANT2_2(pid: One_43);
  requires DecisionChannel[pid->val][NONE()] == 0;
  requires pid(pid->val);
  modifies RequestChannel, DecisionChannel, VoteChannel, votes, decisions;



implementation Civl_PendingAsyncNoninterferenceChecker_PARTICIPANT2_2(pid: One_43)
{
  var Civl_global_old_RequestChannel: [int]int;
  var Civl_global_old_DecisionChannel: [int][decision]int;
  var Civl_global_old_VoteChannel: [vote]int;
  var Civl_global_old_votes: [int]vote;
  var Civl_global_old_decisions: [int]decision;
  var Civl_linear_int_available: [int]bool;

  init:
    Civl_global_old_RequestChannel, Civl_global_old_DecisionChannel, Civl_global_old_VoteChannel, Civl_global_old_votes, Civl_global_old_decisions := RequestChannel, DecisionChannel, VoteChannel, votes, decisions;
    Civl_linear_int_available := MapOr_230(One_Collector_43(pid), MapConst_5_150(false));
    call PARTICIPANT2(pid);
    call Civl_Wrapper_NoninterferenceChecker_2(Civl_linear_int_available, Civl_global_old_RequestChannel, Civl_global_old_DecisionChannel, Civl_global_old_VoteChannel, Civl_global_old_votes, Civl_global_old_decisions);
    return;
}



procedure Civl_PendingAsyncNoninterferenceChecker_COORDINATOR1_2(pid: One_43) returns (Civl_PAs_COORDINATOR2: [COORDINATOR2]int);
  requires pid->val == 0;
  modifies RequestChannel, DecisionChannel, VoteChannel, votes, decisions;



implementation Civl_PendingAsyncNoninterferenceChecker_COORDINATOR1_2(pid: One_43) returns (Civl_PAs_COORDINATOR2: [COORDINATOR2]int)
{
  var Civl_global_old_RequestChannel: [int]int;
  var Civl_global_old_DecisionChannel: [int][decision]int;
  var Civl_global_old_VoteChannel: [vote]int;
  var Civl_global_old_votes: [int]vote;
  var Civl_global_old_decisions: [int]decision;
  var Civl_linear_int_available: [int]bool;

  init:
    Civl_global_old_RequestChannel, Civl_global_old_DecisionChannel, Civl_global_old_VoteChannel, Civl_global_old_votes, Civl_global_old_decisions := RequestChannel, DecisionChannel, VoteChannel, votes, decisions;
    Civl_linear_int_available := MapOr_230(One_Collector_43(pid), MapConst_5_150(false));
    call Civl_PAs_COORDINATOR2 := COORDINATOR1(pid);
    call Civl_Wrapper_NoninterferenceChecker_2(Civl_linear_int_available, Civl_global_old_RequestChannel, Civl_global_old_DecisionChannel, Civl_global_old_VoteChannel, Civl_global_old_votes, Civl_global_old_decisions);
    return;
}



procedure Civl_PendingAsyncNoninterferenceChecker_COORDINATOR2_2(pid: One_43);
  requires pid->val == 0;
  modifies RequestChannel, DecisionChannel, VoteChannel, votes, decisions;



implementation Civl_PendingAsyncNoninterferenceChecker_COORDINATOR2_2(pid: One_43)
{
  var Civl_global_old_RequestChannel: [int]int;
  var Civl_global_old_DecisionChannel: [int][decision]int;
  var Civl_global_old_VoteChannel: [vote]int;
  var Civl_global_old_votes: [int]vote;
  var Civl_global_old_decisions: [int]decision;
  var Civl_linear_int_available: [int]bool;

  init:
    Civl_global_old_RequestChannel, Civl_global_old_DecisionChannel, Civl_global_old_VoteChannel, Civl_global_old_votes, Civl_global_old_decisions := RequestChannel, DecisionChannel, VoteChannel, votes, decisions;
    Civl_linear_int_available := MapOr_230(One_Collector_43(pid), MapConst_5_150(false));
    call COORDINATOR2(pid);
    call Civl_Wrapper_NoninterferenceChecker_2(Civl_linear_int_available, Civl_global_old_RequestChannel, Civl_global_old_DecisionChannel, Civl_global_old_VoteChannel, Civl_global_old_votes, Civl_global_old_decisions);
    return;
}



procedure {:inline 1} Civl_Wrapper_NoninterferenceChecker_2(Civl_linear_int_in: [int]bool, 
    Civl_global_old_RequestChannel: [int]int, 
    Civl_global_old_DecisionChannel: [int][decision]int, 
    Civl_global_old_VoteChannel: [vote]int, 
    Civl_global_old_votes: [int]vote, 
    Civl_global_old_decisions: [int]decision);



implementation Civl_Wrapper_NoninterferenceChecker_2(Civl_Civl_linear_int_in: [int]bool, 
    Civl_Civl_global_old_RequestChannel: [int]int, 
    Civl_Civl_global_old_DecisionChannel: [int][decision]int, 
    Civl_Civl_global_old_VoteChannel: [vote]int, 
    Civl_Civl_global_old_votes: [int]vote, 
    Civl_Civl_global_old_decisions: [int]decision)
{

  enter:
    return;
}



procedure Civl_PendingAsyncNoninterferenceChecker_PARTICIPANT1_3(pid: One_43) returns (Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int);
  requires pid(pid->val);
  modifies RequestChannel, DecisionChannel, VoteChannel, votes, decisions;



implementation Civl_PendingAsyncNoninterferenceChecker_PARTICIPANT1_3(pid: One_43) returns (Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int)
{
  var Civl_global_old_RequestChannel: [int]int;
  var Civl_global_old_DecisionChannel: [int][decision]int;
  var Civl_global_old_VoteChannel: [vote]int;
  var Civl_global_old_votes: [int]vote;
  var Civl_global_old_decisions: [int]decision;
  var Civl_linear_int_available: [int]bool;

  init:
    Civl_global_old_RequestChannel, Civl_global_old_DecisionChannel, Civl_global_old_VoteChannel, Civl_global_old_votes, Civl_global_old_decisions := RequestChannel, DecisionChannel, VoteChannel, votes, decisions;
    Civl_linear_int_available := MapOr_230(One_Collector_43(pid), MapConst_5_150(false));
    call Civl_PAs_PARTICIPANT2 := PARTICIPANT1(pid);
    call Civl_Wrapper_NoninterferenceChecker_3(Civl_linear_int_available, Civl_global_old_RequestChannel, Civl_global_old_DecisionChannel, Civl_global_old_VoteChannel, Civl_global_old_votes, Civl_global_old_decisions);
    return;
}



procedure Civl_PendingAsyncNoninterferenceChecker_PARTICIPANT2_3(pid: One_43);
  requires DecisionChannel[pid->val][NONE()] == 0;
  requires pid(pid->val);
  modifies RequestChannel, DecisionChannel, VoteChannel, votes, decisions;



implementation Civl_PendingAsyncNoninterferenceChecker_PARTICIPANT2_3(pid: One_43)
{
  var Civl_global_old_RequestChannel: [int]int;
  var Civl_global_old_DecisionChannel: [int][decision]int;
  var Civl_global_old_VoteChannel: [vote]int;
  var Civl_global_old_votes: [int]vote;
  var Civl_global_old_decisions: [int]decision;
  var Civl_linear_int_available: [int]bool;

  init:
    Civl_global_old_RequestChannel, Civl_global_old_DecisionChannel, Civl_global_old_VoteChannel, Civl_global_old_votes, Civl_global_old_decisions := RequestChannel, DecisionChannel, VoteChannel, votes, decisions;
    Civl_linear_int_available := MapOr_230(One_Collector_43(pid), MapConst_5_150(false));
    call PARTICIPANT2(pid);
    call Civl_Wrapper_NoninterferenceChecker_3(Civl_linear_int_available, Civl_global_old_RequestChannel, Civl_global_old_DecisionChannel, Civl_global_old_VoteChannel, Civl_global_old_votes, Civl_global_old_decisions);
    return;
}



procedure Civl_PendingAsyncNoninterferenceChecker_COORDINATOR2_3(pid: One_43);
  requires pid->val == 0;
  modifies RequestChannel, DecisionChannel, VoteChannel, votes, decisions;



implementation Civl_PendingAsyncNoninterferenceChecker_COORDINATOR2_3(pid: One_43)
{
  var Civl_global_old_RequestChannel: [int]int;
  var Civl_global_old_DecisionChannel: [int][decision]int;
  var Civl_global_old_VoteChannel: [vote]int;
  var Civl_global_old_votes: [int]vote;
  var Civl_global_old_decisions: [int]decision;
  var Civl_linear_int_available: [int]bool;

  init:
    Civl_global_old_RequestChannel, Civl_global_old_DecisionChannel, Civl_global_old_VoteChannel, Civl_global_old_votes, Civl_global_old_decisions := RequestChannel, DecisionChannel, VoteChannel, votes, decisions;
    Civl_linear_int_available := MapOr_230(One_Collector_43(pid), MapConst_5_150(false));
    call COORDINATOR2(pid);
    call Civl_Wrapper_NoninterferenceChecker_3(Civl_linear_int_available, Civl_global_old_RequestChannel, Civl_global_old_DecisionChannel, Civl_global_old_VoteChannel, Civl_global_old_votes, Civl_global_old_decisions);
    return;
}



procedure {:inline 1} Civl_Wrapper_NoninterferenceChecker_3(Civl_linear_int_in: [int]bool, 
    Civl_global_old_RequestChannel: [int]int, 
    Civl_global_old_DecisionChannel: [int][decision]int, 
    Civl_global_old_VoteChannel: [vote]int, 
    Civl_global_old_votes: [int]vote, 
    Civl_global_old_decisions: [int]decision);



implementation Civl_Wrapper_NoninterferenceChecker_3(Civl_Civl_linear_int_in: [int]bool, 
    Civl_Civl_global_old_RequestChannel: [int]int, 
    Civl_Civl_global_old_DecisionChannel: [int][decision]int, 
    Civl_Civl_global_old_VoteChannel: [vote]int, 
    Civl_Civl_global_old_votes: [int]vote, 
    Civl_Civl_global_old_decisions: [int]decision)
{

  enter:
    return;
}



procedure Civl_PendingAsyncNoninterferenceChecker_PARTICIPANT2_4(pid: One_43);
  requires DecisionChannel[pid->val][NONE()] == 0;
  requires pid(pid->val);
  modifies RequestChannel, DecisionChannel, VoteChannel, votes, decisions;



implementation Civl_PendingAsyncNoninterferenceChecker_PARTICIPANT2_4(pid: One_43)
{
  var Civl_global_old_RequestChannel: [int]int;
  var Civl_global_old_DecisionChannel: [int][decision]int;
  var Civl_global_old_VoteChannel: [vote]int;
  var Civl_global_old_votes: [int]vote;
  var Civl_global_old_decisions: [int]decision;
  var Civl_linear_int_available: [int]bool;

  init:
    Civl_global_old_RequestChannel, Civl_global_old_DecisionChannel, Civl_global_old_VoteChannel, Civl_global_old_votes, Civl_global_old_decisions := RequestChannel, DecisionChannel, VoteChannel, votes, decisions;
    Civl_linear_int_available := MapOr_230(One_Collector_43(pid), MapConst_5_150(false));
    call PARTICIPANT2(pid);
    call Civl_Wrapper_NoninterferenceChecker_4(Civl_linear_int_available, Civl_global_old_RequestChannel, Civl_global_old_DecisionChannel, Civl_global_old_VoteChannel, Civl_global_old_votes, Civl_global_old_decisions);
    return;
}



procedure Civl_PendingAsyncNoninterferenceChecker_COORDINATOR2_4(pid: One_43);
  requires pid->val == 0;
  modifies RequestChannel, DecisionChannel, VoteChannel, votes, decisions;



implementation Civl_PendingAsyncNoninterferenceChecker_COORDINATOR2_4(pid: One_43)
{
  var Civl_global_old_RequestChannel: [int]int;
  var Civl_global_old_DecisionChannel: [int][decision]int;
  var Civl_global_old_VoteChannel: [vote]int;
  var Civl_global_old_votes: [int]vote;
  var Civl_global_old_decisions: [int]decision;
  var Civl_linear_int_available: [int]bool;

  init:
    Civl_global_old_RequestChannel, Civl_global_old_DecisionChannel, Civl_global_old_VoteChannel, Civl_global_old_votes, Civl_global_old_decisions := RequestChannel, DecisionChannel, VoteChannel, votes, decisions;
    Civl_linear_int_available := MapOr_230(One_Collector_43(pid), MapConst_5_150(false));
    call COORDINATOR2(pid);
    call Civl_Wrapper_NoninterferenceChecker_4(Civl_linear_int_available, Civl_global_old_RequestChannel, Civl_global_old_DecisionChannel, Civl_global_old_VoteChannel, Civl_global_old_votes, Civl_global_old_decisions);
    return;
}



procedure {:inline 1} Civl_Wrapper_NoninterferenceChecker_4(Civl_linear_int_in: [int]bool, 
    Civl_global_old_RequestChannel: [int]int, 
    Civl_global_old_DecisionChannel: [int][decision]int, 
    Civl_global_old_VoteChannel: [vote]int, 
    Civl_global_old_votes: [int]vote, 
    Civl_global_old_decisions: [int]decision);



implementation Civl_Wrapper_NoninterferenceChecker_4(Civl_Civl_linear_int_in: [int]bool, 
    Civl_Civl_global_old_RequestChannel: [int]int, 
    Civl_Civl_global_old_DecisionChannel: [int][decision]int, 
    Civl_Civl_global_old_VoteChannel: [vote]int, 
    Civl_Civl_global_old_votes: [int]vote, 
    Civl_Civl_global_old_decisions: [int]decision)
{

  enter:
    return;
}



procedure {:inline 1} Civl_NoninterferenceChecker_yield_YieldParticipant(Civl_linear_int_in: [int]bool, 
    Civl_snapshot_RequestChannel: [int]int, 
    Civl_snapshot_DecisionChannel: [int][decision]int, 
    Civl_snapshot_VoteChannel: [vote]int, 
    Civl_snapshot_votes: [int]vote, 
    Civl_snapshot_decisions: [int]decision);



implementation Civl_NoninterferenceChecker_yield_YieldParticipant(Civl_linear_int_in: [int]bool, 
    Civl_snapshot_RequestChannel: [int]int, 
    Civl_snapshot_DecisionChannel: [int][decision]int, 
    Civl_snapshot_VoteChannel: [vote]int, 
    Civl_snapshot_votes: [int]vote, 
    Civl_snapshot_decisions: [int]decision)
{
  var pid: One_43;

  enter:
    goto exit, L;

  exit:
    return;

  L:
    assume (exists Civl_partition_int: [int]int :: 
      MapImp_230(One_Collector_43(pid), MapEq_230_3(Civl_partition_int, MapConst_2959_2942(0)))
           == MapConst_5_150(true)
         && MapImp_230(Civl_linear_int_in, MapEq_230_3(Civl_partition_int, MapConst_2959_2942(1)))
           == MapConst_5_150(true));
    assume Civl_snapshot_DecisionChannel[pid->val][COMMIT()] > 0
       || Civl_snapshot_DecisionChannel[pid->val][ABORT()] > 0;
    assert DecisionChannel[pid->val][COMMIT()] > 0
       || DecisionChannel[pid->val][ABORT()] > 0;
    assume false;
    return;
}



procedure Civl_PendingAsyncNoninterferenceChecker_PARTICIPANT2_5(pid: One_43);
  requires DecisionChannel[pid->val][NONE()] == 0;
  requires pid(pid->val);
  modifies RequestChannel, DecisionChannel, VoteChannel, votes, decisions;



implementation Civl_PendingAsyncNoninterferenceChecker_PARTICIPANT2_5(pid: One_43)
{
  var Civl_global_old_RequestChannel: [int]int;
  var Civl_global_old_DecisionChannel: [int][decision]int;
  var Civl_global_old_VoteChannel: [vote]int;
  var Civl_global_old_votes: [int]vote;
  var Civl_global_old_decisions: [int]decision;
  var Civl_linear_int_available: [int]bool;

  init:
    Civl_global_old_RequestChannel, Civl_global_old_DecisionChannel, Civl_global_old_VoteChannel, Civl_global_old_votes, Civl_global_old_decisions := RequestChannel, DecisionChannel, VoteChannel, votes, decisions;
    Civl_linear_int_available := MapOr_230(One_Collector_43(pid), MapConst_5_150(false));
    call PARTICIPANT2(pid);
    call Civl_Wrapper_NoninterferenceChecker_5(Civl_linear_int_available, Civl_global_old_RequestChannel, Civl_global_old_DecisionChannel, Civl_global_old_VoteChannel, Civl_global_old_votes, Civl_global_old_decisions);
    return;
}



procedure {:inline 1} Civl_Wrapper_NoninterferenceChecker_5(Civl_linear_int_in: [int]bool, 
    Civl_global_old_RequestChannel: [int]int, 
    Civl_global_old_DecisionChannel: [int][decision]int, 
    Civl_global_old_VoteChannel: [vote]int, 
    Civl_global_old_votes: [int]vote, 
    Civl_global_old_decisions: [int]decision);



implementation Civl_Wrapper_NoninterferenceChecker_5(Civl_Civl_linear_int_in: [int]bool, 
    Civl_Civl_global_old_RequestChannel: [int]int, 
    Civl_Civl_global_old_DecisionChannel: [int][decision]int, 
    Civl_Civl_global_old_VoteChannel: [vote]int, 
    Civl_Civl_global_old_votes: [int]vote, 
    Civl_Civl_global_old_decisions: [int]decision)
{

  enter:
    goto L_0;

  L_0:
    call Civl_NoninterferenceChecker_yield_YieldParticipant(Civl_Civl_linear_int_in, Civl_Civl_global_old_RequestChannel, Civl_Civl_global_old_DecisionChannel, Civl_Civl_global_old_VoteChannel, Civl_Civl_global_old_votes, Civl_Civl_global_old_decisions);
    return;
}



procedure Civl_ISL_base_MAIN4(pids: Set_230) returns (Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int);
  requires (forall k: int :: 
    0 <= k && k <= n
       ==> (forall decisions: [int]decision, votes: [int]vote :: 
        (decisions[0] == COMMIT() || decisions[0] == ABORT())
             && (decisions[0] == COMMIT() ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
             && (forall i: int :: pidLe(i, k) ==> decisions[i] == decisions[0])
           ==> (forall Civl_pa1: PARTICIPANT2, Civl_pa2: PARTICIPANT2 :: 
            (lambda {:pool "PARTICIPANT2"} pa: PARTICIPANT2 :: pidGt(pa->pid->val, k))[Civl_pa1]
                 && (lambda {:pool "PARTICIPANT2"} pa: PARTICIPANT2 :: pidGt(pa->pid->val, k))[Civl_pa2]
                 && Civl_pa1 != Civl_pa2
               ==> Civl_pa1->pid != Civl_pa2->pid)));
  requires (forall k: int :: 
    0 <= k && k <= n
       ==> (forall decisions: [int]decision, votes: [int]vote :: 
        (decisions[0] == COMMIT() || decisions[0] == ABORT())
             && (decisions[0] == COMMIT() ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
             && (forall i: int :: pidLe(i, k) ==> decisions[i] == decisions[0])
           ==> (forall Civl_pa: PARTICIPANT2 :: 
            (lambda {:pool "PARTICIPANT2"} pa: PARTICIPANT2 :: pidGt(pa->pid->val, k))[Civl_pa]
               ==> Set_Contains_43(Set_230((lambda i: int :: k < i && i <= n)), Civl_pa->pid->val))));
  requires (forall k: int :: 
    0 <= k && k <= n
       ==> (forall decisions: [int]decision, votes: [int]vote :: 
        (decisions[0] == COMMIT() || decisions[0] == ABORT())
             && (decisions[0] == COMMIT() ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
             && (forall i: int :: pidLe(i, k) ==> decisions[i] == decisions[0])
           ==> Set_IsSubset_335(Set_230((lambda i: int :: k < i && i <= n)), pids)));
  requires Init(pids->val, RequestChannel, VoteChannel, DecisionChannel, decisions);
  requires true;
  modifies RequestChannel, VoteChannel, DecisionChannel, votes, decisions;



implementation Civl_ISL_base_MAIN4(pids: Set_230) returns (Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int)
{

  ISL_base_MAIN4:
    assert true
       ==> (forall votes: [int]vote :: 
        (COMMIT() == COMMIT()
           ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
           ==> (forall Civl_pa1: PARTICIPANT2, Civl_pa2: PARTICIPANT2 :: 
            (lambda pa: PARTICIPANT2 :: pid(pa->pid->val))[Civl_pa1]
                 && (lambda pa: PARTICIPANT2 :: pid(pa->pid->val))[Civl_pa2]
                 && Civl_pa1 != Civl_pa2
               ==> Civl_pa1->pid != Civl_pa2->pid));
    assert true
       ==> (forall votes: [int]vote :: 
        (COMMIT() == COMMIT()
           ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
           ==> (forall Civl_pa: PARTICIPANT2 :: 
            (lambda pa: PARTICIPANT2 :: pid(pa->pid->val))[Civl_pa]
               ==> Set_Contains_43(Set_230((lambda i: int :: pid(i))), Civl_pa->pid->val)));
    assert true
       ==> (forall votes: [int]vote :: 
        (COMMIT() == COMMIT()
           ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
           ==> Set_IsSubset_335(Set_230((lambda i: int :: pid(i))), pids));
    assert true
       ==> (forall votes: [int]vote :: 
        (ABORT() == COMMIT()
           ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
           ==> (forall Civl_pa1: PARTICIPANT2, Civl_pa2: PARTICIPANT2 :: 
            (lambda pa: PARTICIPANT2 :: pid(pa->pid->val))[Civl_pa1]
                 && (lambda pa: PARTICIPANT2 :: pid(pa->pid->val))[Civl_pa2]
                 && Civl_pa1 != Civl_pa2
               ==> Civl_pa1->pid != Civl_pa2->pid));
    assert true
       ==> (forall votes: [int]vote :: 
        (ABORT() == COMMIT()
           ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
           ==> (forall Civl_pa: PARTICIPANT2 :: 
            (lambda pa: PARTICIPANT2 :: pid(pa->pid->val))[Civl_pa]
               ==> Set_Contains_43(Set_230((lambda i: int :: pid(i))), Civl_pa->pid->val)));
    assert true
       ==> (forall votes: [int]vote :: 
        (ABORT() == COMMIT()
           ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
           ==> Set_IsSubset_335(Set_230((lambda i: int :: pid(i))), pids));
    assert Init(pids->val, RequestChannel, VoteChannel, DecisionChannel, decisions);
    call Civl_PAs_PARTICIPANT2 := MAIN4(pids);
    assert (exists {:pool "INV4"} Civl_k#0: int :: 
      0 <= Civl_k#0
         && Civl_k#0 <= n
         && (decisions[0] == COMMIT() || decisions[0] == ABORT())
         && (decisions[0] == COMMIT() ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
         && (forall i: int :: pidLe(i, Civl_k#0) ==> decisions[i] == decisions[0])
         && DecisionChannel
           == (lambda i: int :: 
            (lambda d: decision :: 
              (if pidGt(i, Civl_k#0) && d == decisions[0] then 1 else 0)))
         && Civl_PAs_PARTICIPANT2
           == MapAdd_14175(MapConst_3_14186(0), 
            MapIte_14193_3((lambda {:pool "PARTICIPANT2"} pa: PARTICIPANT2 :: 
                pidGt(pa->pid->val, Civl_k#0)), 
              MapConst_3_14186(1), 
              MapConst_3_14186(0))));
    return;
}



procedure Civl_ISL_conclusion_MAIN4(pids: Set_230) returns (Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int);
  requires Init(pids->val, RequestChannel, VoteChannel, DecisionChannel, decisions);
  requires true;
  modifies RequestChannel, VoteChannel, DecisionChannel, votes, decisions;



implementation Civl_ISL_conclusion_MAIN4(pids: Set_230) returns (Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int)
{

  ISL_conclusion_MAIN4:
    assert (forall k: int :: 
      0 <= k && k <= n
         ==> (forall decisions: [int]decision, votes: [int]vote :: 
          (decisions[0] == COMMIT() || decisions[0] == ABORT())
               && (decisions[0] == COMMIT() ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
               && (forall i: int :: pidLe(i, k) ==> decisions[i] == decisions[0])
             ==> (forall Civl_pa1: PARTICIPANT2, Civl_pa2: PARTICIPANT2 :: 
              (lambda {:pool "PARTICIPANT2"} pa: PARTICIPANT2 :: pidGt(pa->pid->val, k))[Civl_pa1]
                   && (lambda {:pool "PARTICIPANT2"} pa: PARTICIPANT2 :: pidGt(pa->pid->val, k))[Civl_pa2]
                   && Civl_pa1 != Civl_pa2
                 ==> Civl_pa1->pid != Civl_pa2->pid)));
    assert (forall k: int :: 
      0 <= k && k <= n
         ==> (forall decisions: [int]decision, votes: [int]vote :: 
          (decisions[0] == COMMIT() || decisions[0] == ABORT())
               && (decisions[0] == COMMIT() ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
               && (forall i: int :: pidLe(i, k) ==> decisions[i] == decisions[0])
             ==> (forall Civl_pa: PARTICIPANT2 :: 
              (lambda {:pool "PARTICIPANT2"} pa: PARTICIPANT2 :: pidGt(pa->pid->val, k))[Civl_pa]
                 ==> Set_Contains_43(Set_230((lambda i: int :: k < i && i <= n)), Civl_pa->pid->val))));
    assert (forall k: int :: 
      0 <= k && k <= n
         ==> (forall decisions: [int]decision, votes: [int]vote :: 
          (decisions[0] == COMMIT() || decisions[0] == ABORT())
               && (decisions[0] == COMMIT() ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
               && (forall i: int :: pidLe(i, k) ==> decisions[i] == decisions[0])
             ==> Set_IsSubset_335(Set_230((lambda i: int :: k < i && i <= n)), pids)));
    assert Init(pids->val, RequestChannel, VoteChannel, DecisionChannel, decisions);
    call Civl_PAs_PARTICIPANT2 := INV4(pids);
    assume Civl_PAs_PARTICIPANT2 == MapConst_3_14186(0);
    assert (
        (COMMIT() == COMMIT() ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
         && (forall i: int :: i == 0 || pid(i) ==> decisions[i] == COMMIT())
         && DecisionChannel == old(DecisionChannel))
       || (
        (ABORT() == COMMIT() ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
         && (forall i: int :: i == 0 || pid(i) ==> decisions[i] == ABORT())
         && DecisionChannel == old(DecisionChannel));
    return;
}



procedure Civl_ISL_step_INV4_PARTICIPANT2(pids: Set_230)
   returns (Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int, Civl_choice: Choice_INV4);
  requires (forall k: int :: 
    0 <= k && k <= n
       ==> (forall decisions: [int]decision, votes: [int]vote :: 
        (decisions[0] == COMMIT() || decisions[0] == ABORT())
             && (decisions[0] == COMMIT() ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
             && (forall i: int :: pidLe(i, k) ==> decisions[i] == decisions[0])
           ==> (forall Civl_pa1: PARTICIPANT2, Civl_pa2: PARTICIPANT2 :: 
            (lambda {:pool "PARTICIPANT2"} pa: PARTICIPANT2 :: pidGt(pa->pid->val, k))[Civl_pa1]
                 && (lambda {:pool "PARTICIPANT2"} pa: PARTICIPANT2 :: pidGt(pa->pid->val, k))[Civl_pa2]
                 && Civl_pa1 != Civl_pa2
               ==> Civl_pa1->pid != Civl_pa2->pid)));
  requires (forall k: int :: 
    0 <= k && k <= n
       ==> (forall decisions: [int]decision, votes: [int]vote :: 
        (decisions[0] == COMMIT() || decisions[0] == ABORT())
             && (decisions[0] == COMMIT() ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
             && (forall i: int :: pidLe(i, k) ==> decisions[i] == decisions[0])
           ==> (forall Civl_pa: PARTICIPANT2 :: 
            (lambda {:pool "PARTICIPANT2"} pa: PARTICIPANT2 :: pidGt(pa->pid->val, k))[Civl_pa]
               ==> Set_Contains_43(Set_230((lambda i: int :: k < i && i <= n)), Civl_pa->pid->val))));
  requires (forall k: int :: 
    0 <= k && k <= n
       ==> (forall decisions: [int]decision, votes: [int]vote :: 
        (decisions[0] == COMMIT() || decisions[0] == ABORT())
             && (decisions[0] == COMMIT() ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
             && (forall i: int :: pidLe(i, k) ==> decisions[i] == decisions[0])
           ==> Set_IsSubset_335(Set_230((lambda i: int :: k < i && i <= n)), pids)));
  requires Init(pids->val, RequestChannel, VoteChannel, DecisionChannel, decisions);
  requires true;
  modifies RequestChannel, VoteChannel, DecisionChannel, votes, decisions;



implementation Civl_ISL_step_INV4_PARTICIPANT2(pids: Set_230)
   returns (Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int, Civl_choice: Choice_INV4)
{

  ISL_step_INV4_PARTICIPANT2:
    call Civl_PAs_PARTICIPANT2, Civl_choice := INV4_With_Choice(pids);
    assume Civl_choice is Choice_INV4_PARTICIPANT2;
    assume Civl_PAs_PARTICIPANT2[Civl_choice->PARTICIPANT2] > 0;
    Civl_PAs_PARTICIPANT2[Civl_choice->PARTICIPANT2] := Civl_PAs_PARTICIPANT2[Civl_choice->PARTICIPANT2] - 1;
    assert DecisionChannel[Civl_choice->PARTICIPANT2->pid->val][NONE()] == 0;
    assert pid(Civl_choice->PARTICIPANT2->pid->val);
    assert DecisionChannel[Civl_choice->PARTICIPANT2->pid->val][COMMIT()] > 0
       || DecisionChannel[Civl_choice->PARTICIPANT2->pid->val][ABORT()] > 0;
    call PARTICIPANT2(Civl_choice->PARTICIPANT2->pid);
    assert (exists {:pool "INV4"} Civl_k#0: int :: 
      0 <= Civl_k#0
         && Civl_k#0 <= n
         && (decisions[0] == COMMIT() || decisions[0] == ABORT())
         && (decisions[0] == COMMIT() ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
         && (forall i: int :: pidLe(i, Civl_k#0) ==> decisions[i] == decisions[0])
         && DecisionChannel
           == (lambda i: int :: 
            (lambda d: decision :: 
              (if pidGt(i, Civl_k#0) && d == decisions[0] then 1 else 0)))
         && Civl_PAs_PARTICIPANT2
           == MapAdd_14175(MapConst_3_14186(0), 
            MapIte_14193_3((lambda {:pool "PARTICIPANT2"} pa: PARTICIPANT2 :: 
                pidGt(pa->pid->val, Civl_k#0)), 
              MapConst_3_14186(1), 
              MapConst_3_14186(0))));
    return;
}



implementation MAIN3_RefinementCheck(pids: Set_230) returns (Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int)
{
  var pids': Set_230;
  var pid: One_43;
  var participantPids: Set_230;
  var inline$COORDINATOR2_RefinementCheck$0$dec: decision;
  var inline$COORDINATOR2_RefinementCheck$0$pid: One_43;
  var inline$COORDINATOR2_RefinementCheck$0$VoteChannel: [vote]int;
  var inline$COORDINATOR2_RefinementCheck$0$DecisionChannel: [int][decision]int;
  var inline$COORDINATOR2_RefinementCheck$0$decisions: [int]decision;

  /*** structured program:
    assert Init(pids->val, RequestChannel, VoteChannel, DecisionChannel, decisions);
    havoc RequestChannel, VoteChannel, votes;
    assume VoteChannel[YES()] >= 0 && VoteChannel[NO()] >= 0;
    assume VoteChannel[YES()] + VoteChannel[NO()] <= n;
    assume VoteChannel[YES()] == n ==> (forall i: int :: pid(i) ==> votes[i] == YES());
    pids' := pids;
    call pid := One_Get_687(pids', 0);
    async call COORDINATOR2(pid);
    call participantPids := Set_Get_335(pids', (lambda i: int :: pid(i)));
    call {:linear participantPids} create_asyncs_4801((lambda pa: PARTICIPANT2 :: pid(pa->pid->val)));
  **** end structured program */

  anon0:
    Civl_PAs_PARTICIPANT2 := MapConst_3_14186(0);
    assert Init(pids->val, RequestChannel, VoteChannel, DecisionChannel, decisions);
    havoc RequestChannel, VoteChannel, votes;
    assume VoteChannel[YES()] >= 0 && VoteChannel[NO()] >= 0;
    assume VoteChannel[YES()] + VoteChannel[NO()] <= n;
    assume VoteChannel[YES()] == n ==> (forall i: int :: pid(i) ==> votes[i] == YES());
    pids' := pids;
    assert Set_Contains_43(pids', 0);
    pids' := Set_Remove_687(pids', 0);
    pid := One_43(0);
    goto inline$COORDINATOR2_RefinementCheck$0$Entry;

  inline$COORDINATOR2_RefinementCheck$0$Entry:
    inline$COORDINATOR2_RefinementCheck$0$pid := pid;
    havoc inline$COORDINATOR2_RefinementCheck$0$dec;
    inline$COORDINATOR2_RefinementCheck$0$VoteChannel := VoteChannel;
    inline$COORDINATOR2_RefinementCheck$0$DecisionChannel := DecisionChannel;
    inline$COORDINATOR2_RefinementCheck$0$decisions := decisions;
    goto inline$COORDINATOR2_RefinementCheck$0$anon0;

  inline$COORDINATOR2_RefinementCheck$0$anon0:
    assert inline$COORDINATOR2_RefinementCheck$0$pid->val == 0;
    goto inline$COORDINATOR2_RefinementCheck$0$anon4_Then, inline$COORDINATOR2_RefinementCheck$0$anon4_Else;

  inline$COORDINATOR2_RefinementCheck$0$anon4_Else:
    inline$COORDINATOR2_RefinementCheck$0$dec := ABORT();
    goto inline$COORDINATOR2_RefinementCheck$0$anon3;

  inline$COORDINATOR2_RefinementCheck$0$anon3:
    decisions[inline$COORDINATOR2_RefinementCheck$0$pid->val] := inline$COORDINATOR2_RefinementCheck$0$dec;
    havoc VoteChannel;
    DecisionChannel := (lambda inline$COORDINATOR2_RefinementCheck$0$i: int :: 
      (lambda inline$COORDINATOR2_RefinementCheck$0$d: decision :: 
        (if pid(inline$COORDINATOR2_RefinementCheck$0$i)
             && inline$COORDINATOR2_RefinementCheck$0$d
               == inline$COORDINATOR2_RefinementCheck$0$dec
           then DecisionChannel[inline$COORDINATOR2_RefinementCheck$0$i][inline$COORDINATOR2_RefinementCheck$0$d]
             + 1
           else DecisionChannel[inline$COORDINATOR2_RefinementCheck$0$i][inline$COORDINATOR2_RefinementCheck$0$d])));
    goto inline$COORDINATOR2_RefinementCheck$0$Return;

  inline$COORDINATOR2_RefinementCheck$0$anon4_Then:
    assume VoteChannel[YES()] >= n;
    inline$COORDINATOR2_RefinementCheck$0$dec := COMMIT();
    goto inline$COORDINATOR2_RefinementCheck$0$anon3;

  inline$COORDINATOR2_RefinementCheck$0$Return:
    goto anon0$1;

  anon0$1:
    participantPids := Set_230((lambda i: int :: pid(i)));
    assert Set_IsSubset_335(participantPids, pids');
    pids' := Set_Difference_335(pids', participantPids);
    assert (forall Civl_pa: PARTICIPANT2 :: 
      (lambda pa: PARTICIPANT2 :: pid(pa->pid->val))[Civl_pa]
         ==> Set_Contains_43(participantPids, Civl_pa->pid->val));
    assert (forall Civl_pa1: PARTICIPANT2, Civl_pa2: PARTICIPANT2 :: 
      (lambda pa: PARTICIPANT2 :: pid(pa->pid->val))[Civl_pa1]
           && (lambda pa: PARTICIPANT2 :: pid(pa->pid->val))[Civl_pa2]
           && Civl_pa1 != Civl_pa2
         ==> Civl_pa1->pid != Civl_pa2->pid);
    Civl_PAs_PARTICIPANT2 := MapAdd_14175(Civl_PAs_PARTICIPANT2, 
      MapIte_14193_3((lambda pa: PARTICIPANT2 :: pid(pa->pid->val)), 
        MapConst_3_14186(1), 
        MapConst_3_14186(0)));
    return;
}



procedure MAIN3_RefinementCheck(pids: Set_230) returns (Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int);
  requires true
     ==> (forall votes: [int]vote :: 
      (COMMIT() == COMMIT()
         ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
         ==> (forall Civl_pa1: PARTICIPANT2, Civl_pa2: PARTICIPANT2 :: 
          (lambda pa: PARTICIPANT2 :: pid(pa->pid->val))[Civl_pa1]
               && (lambda pa: PARTICIPANT2 :: pid(pa->pid->val))[Civl_pa2]
               && Civl_pa1 != Civl_pa2
             ==> Civl_pa1->pid != Civl_pa2->pid));
  requires true
     ==> (forall votes: [int]vote :: 
      (COMMIT() == COMMIT()
         ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
         ==> (forall Civl_pa: PARTICIPANT2 :: 
          (lambda pa: PARTICIPANT2 :: pid(pa->pid->val))[Civl_pa]
             ==> Set_Contains_43(Set_230((lambda i: int :: pid(i))), Civl_pa->pid->val)));
  requires true
     ==> (forall votes: [int]vote :: 
      (COMMIT() == COMMIT()
         ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
         ==> Set_IsSubset_335(Set_230((lambda i: int :: pid(i))), pids));
  requires true
     ==> (forall votes: [int]vote :: 
      (ABORT() == COMMIT()
         ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
         ==> (forall Civl_pa1: PARTICIPANT2, Civl_pa2: PARTICIPANT2 :: 
          (lambda pa: PARTICIPANT2 :: pid(pa->pid->val))[Civl_pa1]
               && (lambda pa: PARTICIPANT2 :: pid(pa->pid->val))[Civl_pa2]
               && Civl_pa1 != Civl_pa2
             ==> Civl_pa1->pid != Civl_pa2->pid));
  requires true
     ==> (forall votes: [int]vote :: 
      (ABORT() == COMMIT()
         ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
         ==> (forall Civl_pa: PARTICIPANT2 :: 
          (lambda pa: PARTICIPANT2 :: pid(pa->pid->val))[Civl_pa]
             ==> Set_Contains_43(Set_230((lambda i: int :: pid(i))), Civl_pa->pid->val)));
  requires true
     ==> (forall votes: [int]vote :: 
      (ABORT() == COMMIT()
         ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
         ==> Set_IsSubset_335(Set_230((lambda i: int :: pid(i))), pids));
  requires Init(pids->val, RequestChannel, VoteChannel, DecisionChannel, decisions);
  modifies RequestChannel, VoteChannel, votes, DecisionChannel, decisions;
  ensures (
      true
       && (COMMIT() == COMMIT() ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
       && decisions == old(decisions)[0 := COMMIT()]
       && DecisionChannel
         == (lambda i: int :: 
          (lambda d: decision :: (if pid(i) && d == COMMIT() then 1 else 0)))
       && Civl_PAs_PARTICIPANT2
         == MapAdd_14175(MapConst_3_14186(0), 
          MapIte_14193_3((lambda pa: PARTICIPANT2 :: pid(pa->pid->val)), 
            MapConst_3_14186(1), 
            MapConst_3_14186(0))))
     || (
      true
       && (ABORT() == COMMIT() ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
       && decisions == old(decisions)[0 := ABORT()]
       && DecisionChannel
         == (lambda i: int :: 
          (lambda d: decision :: (if pid(i) && d == ABORT() then 1 else 0)))
       && Civl_PAs_PARTICIPANT2
         == MapAdd_14175(MapConst_3_14186(0), 
          MapIte_14193_3((lambda pa: PARTICIPANT2 :: pid(pa->pid->val)), 
            MapConst_3_14186(1), 
            MapConst_3_14186(0))));



procedure Civl_ISL_base_MAIN2(pids: Set_230)
   returns (Civl_PAs_COORDINATOR2: [COORDINATOR2]int, 
    Civl_PAs_PARTICIPANT1: [PARTICIPANT1]int, 
    Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int);
  requires (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
    0 <= k && k <= n
       ==> 
      (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
         && VoteChannel[YES()] >= 0
         && VoteChannel[NO()] >= 0
         && VoteChannel[YES()] + VoteChannel[NO()] <= k
         && (VoteChannel[YES()] == k
           ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
       ==> (forall Civl_pa1: PARTICIPANT1, Civl_pa2: PARTICIPANT1 :: 
        (lambda {:pool "PARTICIPANT1"} pa: PARTICIPANT1 :: pidGt(pa->pid->val, k))[Civl_pa1]
             && (lambda {:pool "PARTICIPANT1"} pa: PARTICIPANT1 :: pidGt(pa->pid->val, k))[Civl_pa2]
             && Civl_pa1 != Civl_pa2
           ==> Civl_pa1->pid != Civl_pa2->pid));
  requires (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
    0 <= k && k <= n
       ==> 
      (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
         && VoteChannel[YES()] >= 0
         && VoteChannel[NO()] >= 0
         && VoteChannel[YES()] + VoteChannel[NO()] <= k
         && (VoteChannel[YES()] == k
           ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
       ==> (forall Civl_pa: PARTICIPANT1 :: 
        (lambda {:pool "PARTICIPANT1"} pa: PARTICIPANT1 :: pidGt(pa->pid->val, k))[Civl_pa]
           ==> Set_Contains_43(Set_230((lambda i: int :: k < i && i <= n)), Civl_pa->pid->val)));
  requires (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
    0 <= k && k <= n
       ==> 
      (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
         && VoteChannel[YES()] >= 0
         && VoteChannel[NO()] >= 0
         && VoteChannel[YES()] + VoteChannel[NO()] <= k
         && (VoteChannel[YES()] == k
           ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
       ==> Set_IsSubset_335(Set_230((lambda i: int :: k < i && i <= n)), 
        Set_Difference_335(Set_Remove_687(pids, 0), Set_230((lambda i: int :: 1 <= i && i <= k)))));
  requires (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
    0 <= k && k <= n
       ==> 
      (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
         && VoteChannel[YES()] >= 0
         && VoteChannel[NO()] >= 0
         && VoteChannel[YES()] + VoteChannel[NO()] <= k
         && (VoteChannel[YES()] == k
           ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
       ==> (forall Civl_pa1: PARTICIPANT2, Civl_pa2: PARTICIPANT2 :: 
        (lambda pa: PARTICIPANT2 :: pidLe(pa->pid->val, k))[Civl_pa1]
             && (lambda pa: PARTICIPANT2 :: pidLe(pa->pid->val, k))[Civl_pa2]
             && Civl_pa1 != Civl_pa2
           ==> Civl_pa1->pid != Civl_pa2->pid));
  requires (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
    0 <= k && k <= n
       ==> 
      (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
         && VoteChannel[YES()] >= 0
         && VoteChannel[NO()] >= 0
         && VoteChannel[YES()] + VoteChannel[NO()] <= k
         && (VoteChannel[YES()] == k
           ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
       ==> (forall Civl_pa: PARTICIPANT2 :: 
        (lambda pa: PARTICIPANT2 :: pidLe(pa->pid->val, k))[Civl_pa]
           ==> Set_Contains_43(Set_230((lambda i: int :: 1 <= i && i <= k)), Civl_pa->pid->val)));
  requires (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
    0 <= k && k <= n
       ==> 
      (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
         && VoteChannel[YES()] >= 0
         && VoteChannel[NO()] >= 0
         && VoteChannel[YES()] + VoteChannel[NO()] <= k
         && (VoteChannel[YES()] == k
           ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
       ==> Set_IsSubset_335(Set_230((lambda i: int :: 1 <= i && i <= k)), Set_Remove_687(pids, 0)));
  requires (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
    0 <= k && k <= n
       ==> 
      (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
         && VoteChannel[YES()] >= 0
         && VoteChannel[NO()] >= 0
         && VoteChannel[YES()] + VoteChannel[NO()] <= k
         && (VoteChannel[YES()] == k
           ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
       ==> Set_Contains_43(pids, 0));
  requires Init(pids->val, RequestChannel, VoteChannel, DecisionChannel, decisions);
  requires true;
  modifies RequestChannel, VoteChannel, votes;



implementation Civl_ISL_base_MAIN2(pids: Set_230)
   returns (Civl_PAs_COORDINATOR2: [COORDINATOR2]int, 
    Civl_PAs_PARTICIPANT1: [PARTICIPANT1]int, 
    Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int)
{

  ISL_base_MAIN2:
    assert true
       ==> (forall Civl_pa1: PARTICIPANT1, Civl_pa2: PARTICIPANT1 :: 
        (lambda pa: PARTICIPANT1 :: pid(pa->pid->val))[Civl_pa1]
             && (lambda pa: PARTICIPANT1 :: pid(pa->pid->val))[Civl_pa2]
             && Civl_pa1 != Civl_pa2
           ==> Civl_pa1->pid != Civl_pa2->pid);
    assert true
       ==> (forall Civl_pa: PARTICIPANT1 :: 
        (lambda pa: PARTICIPANT1 :: pid(pa->pid->val))[Civl_pa]
           ==> Set_Contains_43(Set_230((lambda i: int :: pid(i))), Civl_pa->pid->val));
    assert true
       ==> Set_IsSubset_335(Set_230((lambda i: int :: pid(i))), Set_Remove_687(pids, 0));
    assert true ==> Set_Contains_43(pids, 0);
    assert Init(pids->val, RequestChannel, VoteChannel, DecisionChannel, decisions);
    call Civl_PAs_COORDINATOR2, Civl_PAs_PARTICIPANT1 := MAIN2(pids);
    Civl_PAs_PARTICIPANT2 := MapConst_3_14186(0);
    assert (exists {:pool "INV2"} Civl_k#0: int :: 
      0 <= Civl_k#0
         && Civl_k#0 <= n
         && (forall i: int :: pidGt(i, Civl_k#0) ==> RequestChannel[i] == 1)
         && VoteChannel[YES()] >= 0
         && VoteChannel[NO()] >= 0
         && VoteChannel[YES()] + VoteChannel[NO()] <= Civl_k#0
         && (VoteChannel[YES()] == Civl_k#0
           ==> (forall i: int :: pidLe(i, Civl_k#0) ==> votes[i] == YES()))
         && Civl_PAs_COORDINATOR2
           == MapAdd_14233(MapConst_3_14244(0), MapConst_3_14244(0)[COORDINATOR2(One_43(0)) := 1])
         && Civl_PAs_PARTICIPANT2
           == MapAdd_14175(MapConst_3_14186(0), 
            MapIte_14193_3((lambda pa: PARTICIPANT2 :: pidLe(pa->pid->val, Civl_k#0)), 
              MapConst_3_14186(1), 
              MapConst_3_14186(0)))
         && Civl_PAs_PARTICIPANT1
           == MapAdd_14143(MapConst_3_14154(0), 
            MapIte_14161_3((lambda {:pool "PARTICIPANT1"} pa: PARTICIPANT1 :: 
                pidGt(pa->pid->val, Civl_k#0)), 
              MapConst_3_14154(1), 
              MapConst_3_14154(0))));
    return;
}



procedure Civl_ISL_conclusion_MAIN2(pids: Set_230)
   returns (Civl_PAs_COORDINATOR2: [COORDINATOR2]int, 
    Civl_PAs_PARTICIPANT1: [PARTICIPANT1]int, 
    Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int);
  requires (forall VoteChannel: [vote]int, votes: [int]vote :: 
    VoteChannel[YES()] >= 0 && VoteChannel[NO()] >= 0
       ==> 
      VoteChannel[YES()] + VoteChannel[NO()] <= n
       ==> 
      (VoteChannel[YES()] == n
       ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
       ==> (forall Civl_pa1: PARTICIPANT2, Civl_pa2: PARTICIPANT2 :: 
        (lambda pa: PARTICIPANT2 :: pid(pa->pid->val))[Civl_pa1]
             && (lambda pa: PARTICIPANT2 :: pid(pa->pid->val))[Civl_pa2]
             && Civl_pa1 != Civl_pa2
           ==> Civl_pa1->pid != Civl_pa2->pid));
  requires (forall VoteChannel: [vote]int, votes: [int]vote :: 
    VoteChannel[YES()] >= 0 && VoteChannel[NO()] >= 0
       ==> 
      VoteChannel[YES()] + VoteChannel[NO()] <= n
       ==> 
      (VoteChannel[YES()] == n
       ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
       ==> (forall Civl_pa: PARTICIPANT2 :: 
        (lambda pa: PARTICIPANT2 :: pid(pa->pid->val))[Civl_pa]
           ==> Set_Contains_43(Set_230((lambda i: int :: pid(i))), Civl_pa->pid->val)));
  requires (forall VoteChannel: [vote]int, votes: [int]vote :: 
    VoteChannel[YES()] >= 0 && VoteChannel[NO()] >= 0
       ==> 
      VoteChannel[YES()] + VoteChannel[NO()] <= n
       ==> 
      (VoteChannel[YES()] == n
       ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
       ==> Set_IsSubset_335(Set_230((lambda i: int :: pid(i))), Set_Remove_687(pids, 0)));
  requires (forall VoteChannel: [vote]int, votes: [int]vote :: 
    VoteChannel[YES()] >= 0 && VoteChannel[NO()] >= 0
       ==> 
      VoteChannel[YES()] + VoteChannel[NO()] <= n
       ==> 
      (VoteChannel[YES()] == n
       ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
       ==> Set_Contains_43(pids, 0));
  requires Init(pids->val, RequestChannel, VoteChannel, DecisionChannel, decisions);
  requires true;
  modifies RequestChannel, VoteChannel, votes;



implementation Civl_ISL_conclusion_MAIN2(pids: Set_230)
   returns (Civl_PAs_COORDINATOR2: [COORDINATOR2]int, 
    Civl_PAs_PARTICIPANT1: [PARTICIPANT1]int, 
    Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int)
{

  ISL_conclusion_MAIN2:
    assert (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
      0 <= k && k <= n
         ==> 
        (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
           && VoteChannel[YES()] >= 0
           && VoteChannel[NO()] >= 0
           && VoteChannel[YES()] + VoteChannel[NO()] <= k
           && (VoteChannel[YES()] == k
             ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
         ==> (forall Civl_pa1: PARTICIPANT1, Civl_pa2: PARTICIPANT1 :: 
          (lambda {:pool "PARTICIPANT1"} pa: PARTICIPANT1 :: pidGt(pa->pid->val, k))[Civl_pa1]
               && (lambda {:pool "PARTICIPANT1"} pa: PARTICIPANT1 :: pidGt(pa->pid->val, k))[Civl_pa2]
               && Civl_pa1 != Civl_pa2
             ==> Civl_pa1->pid != Civl_pa2->pid));
    assert (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
      0 <= k && k <= n
         ==> 
        (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
           && VoteChannel[YES()] >= 0
           && VoteChannel[NO()] >= 0
           && VoteChannel[YES()] + VoteChannel[NO()] <= k
           && (VoteChannel[YES()] == k
             ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
         ==> (forall Civl_pa: PARTICIPANT1 :: 
          (lambda {:pool "PARTICIPANT1"} pa: PARTICIPANT1 :: pidGt(pa->pid->val, k))[Civl_pa]
             ==> Set_Contains_43(Set_230((lambda i: int :: k < i && i <= n)), Civl_pa->pid->val)));
    assert (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
      0 <= k && k <= n
         ==> 
        (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
           && VoteChannel[YES()] >= 0
           && VoteChannel[NO()] >= 0
           && VoteChannel[YES()] + VoteChannel[NO()] <= k
           && (VoteChannel[YES()] == k
             ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
         ==> Set_IsSubset_335(Set_230((lambda i: int :: k < i && i <= n)), 
          Set_Difference_335(Set_Remove_687(pids, 0), Set_230((lambda i: int :: 1 <= i && i <= k)))));
    assert (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
      0 <= k && k <= n
         ==> 
        (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
           && VoteChannel[YES()] >= 0
           && VoteChannel[NO()] >= 0
           && VoteChannel[YES()] + VoteChannel[NO()] <= k
           && (VoteChannel[YES()] == k
             ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
         ==> (forall Civl_pa1: PARTICIPANT2, Civl_pa2: PARTICIPANT2 :: 
          (lambda pa: PARTICIPANT2 :: pidLe(pa->pid->val, k))[Civl_pa1]
               && (lambda pa: PARTICIPANT2 :: pidLe(pa->pid->val, k))[Civl_pa2]
               && Civl_pa1 != Civl_pa2
             ==> Civl_pa1->pid != Civl_pa2->pid));
    assert (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
      0 <= k && k <= n
         ==> 
        (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
           && VoteChannel[YES()] >= 0
           && VoteChannel[NO()] >= 0
           && VoteChannel[YES()] + VoteChannel[NO()] <= k
           && (VoteChannel[YES()] == k
             ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
         ==> (forall Civl_pa: PARTICIPANT2 :: 
          (lambda pa: PARTICIPANT2 :: pidLe(pa->pid->val, k))[Civl_pa]
             ==> Set_Contains_43(Set_230((lambda i: int :: 1 <= i && i <= k)), Civl_pa->pid->val)));
    assert (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
      0 <= k && k <= n
         ==> 
        (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
           && VoteChannel[YES()] >= 0
           && VoteChannel[NO()] >= 0
           && VoteChannel[YES()] + VoteChannel[NO()] <= k
           && (VoteChannel[YES()] == k
             ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
         ==> Set_IsSubset_335(Set_230((lambda i: int :: 1 <= i && i <= k)), Set_Remove_687(pids, 0)));
    assert (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
      0 <= k && k <= n
         ==> 
        (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
           && VoteChannel[YES()] >= 0
           && VoteChannel[NO()] >= 0
           && VoteChannel[YES()] + VoteChannel[NO()] <= k
           && (VoteChannel[YES()] == k
             ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
         ==> Set_Contains_43(pids, 0));
    assert Init(pids->val, RequestChannel, VoteChannel, DecisionChannel, decisions);
    call Civl_PAs_COORDINATOR2, Civl_PAs_PARTICIPANT1, Civl_PAs_PARTICIPANT2 := INV2(pids);
    assume Civl_PAs_PARTICIPANT1 == MapConst_3_14154(0);
    assert VoteChannel[YES()] >= 0
       && VoteChannel[NO()] >= 0
       && VoteChannel[YES()] + VoteChannel[NO()] <= n
       && (VoteChannel[YES()] == n ==> (forall i: int :: pid(i) ==> votes[i] == YES()))
       && Civl_PAs_COORDINATOR2
         == MapAdd_14233(MapConst_3_14244(0), MapConst_3_14244(0)[COORDINATOR2(One_43(0)) := 1])
       && Civl_PAs_PARTICIPANT2
         == MapAdd_14175(MapConst_3_14186(0), 
          MapIte_14193_3((lambda pa: PARTICIPANT2 :: pid(pa->pid->val)), 
            MapConst_3_14186(1), 
            MapConst_3_14186(0)))
       && DecisionChannel == old(DecisionChannel)
       && decisions == old(decisions);
    return;
}



procedure Civl_ISL_step_INV2_PARTICIPANT1(pids: Set_230)
   returns (Civl_PAs_COORDINATOR2: [COORDINATOR2]int, 
    Civl_PAs_PARTICIPANT1: [PARTICIPANT1]int, 
    Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int, 
    Civl_choice: Choice_INV2);
  requires (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
    0 <= k && k <= n
       ==> 
      (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
         && VoteChannel[YES()] >= 0
         && VoteChannel[NO()] >= 0
         && VoteChannel[YES()] + VoteChannel[NO()] <= k
         && (VoteChannel[YES()] == k
           ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
       ==> (forall Civl_pa1: PARTICIPANT1, Civl_pa2: PARTICIPANT1 :: 
        (lambda {:pool "PARTICIPANT1"} pa: PARTICIPANT1 :: pidGt(pa->pid->val, k))[Civl_pa1]
             && (lambda {:pool "PARTICIPANT1"} pa: PARTICIPANT1 :: pidGt(pa->pid->val, k))[Civl_pa2]
             && Civl_pa1 != Civl_pa2
           ==> Civl_pa1->pid != Civl_pa2->pid));
  requires (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
    0 <= k && k <= n
       ==> 
      (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
         && VoteChannel[YES()] >= 0
         && VoteChannel[NO()] >= 0
         && VoteChannel[YES()] + VoteChannel[NO()] <= k
         && (VoteChannel[YES()] == k
           ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
       ==> (forall Civl_pa: PARTICIPANT1 :: 
        (lambda {:pool "PARTICIPANT1"} pa: PARTICIPANT1 :: pidGt(pa->pid->val, k))[Civl_pa]
           ==> Set_Contains_43(Set_230((lambda i: int :: k < i && i <= n)), Civl_pa->pid->val)));
  requires (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
    0 <= k && k <= n
       ==> 
      (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
         && VoteChannel[YES()] >= 0
         && VoteChannel[NO()] >= 0
         && VoteChannel[YES()] + VoteChannel[NO()] <= k
         && (VoteChannel[YES()] == k
           ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
       ==> Set_IsSubset_335(Set_230((lambda i: int :: k < i && i <= n)), 
        Set_Difference_335(Set_Remove_687(pids, 0), Set_230((lambda i: int :: 1 <= i && i <= k)))));
  requires (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
    0 <= k && k <= n
       ==> 
      (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
         && VoteChannel[YES()] >= 0
         && VoteChannel[NO()] >= 0
         && VoteChannel[YES()] + VoteChannel[NO()] <= k
         && (VoteChannel[YES()] == k
           ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
       ==> (forall Civl_pa1: PARTICIPANT2, Civl_pa2: PARTICIPANT2 :: 
        (lambda pa: PARTICIPANT2 :: pidLe(pa->pid->val, k))[Civl_pa1]
             && (lambda pa: PARTICIPANT2 :: pidLe(pa->pid->val, k))[Civl_pa2]
             && Civl_pa1 != Civl_pa2
           ==> Civl_pa1->pid != Civl_pa2->pid));
  requires (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
    0 <= k && k <= n
       ==> 
      (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
         && VoteChannel[YES()] >= 0
         && VoteChannel[NO()] >= 0
         && VoteChannel[YES()] + VoteChannel[NO()] <= k
         && (VoteChannel[YES()] == k
           ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
       ==> (forall Civl_pa: PARTICIPANT2 :: 
        (lambda pa: PARTICIPANT2 :: pidLe(pa->pid->val, k))[Civl_pa]
           ==> Set_Contains_43(Set_230((lambda i: int :: 1 <= i && i <= k)), Civl_pa->pid->val)));
  requires (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
    0 <= k && k <= n
       ==> 
      (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
         && VoteChannel[YES()] >= 0
         && VoteChannel[NO()] >= 0
         && VoteChannel[YES()] + VoteChannel[NO()] <= k
         && (VoteChannel[YES()] == k
           ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
       ==> Set_IsSubset_335(Set_230((lambda i: int :: 1 <= i && i <= k)), Set_Remove_687(pids, 0)));
  requires (forall k: int, RequestChannel: [int]int, VoteChannel: [vote]int, votes: [int]vote :: 
    0 <= k && k <= n
       ==> 
      (forall i: int :: pidGt(i, k) ==> RequestChannel[i] == 1)
         && VoteChannel[YES()] >= 0
         && VoteChannel[NO()] >= 0
         && VoteChannel[YES()] + VoteChannel[NO()] <= k
         && (VoteChannel[YES()] == k
           ==> (forall i: int :: pidLe(i, k) ==> votes[i] == YES()))
       ==> Set_Contains_43(pids, 0));
  requires Init(pids->val, RequestChannel, VoteChannel, DecisionChannel, decisions);
  requires true;
  modifies RequestChannel, VoteChannel, votes;



implementation Civl_ISL_step_INV2_PARTICIPANT1(pids: Set_230)
   returns (Civl_PAs_COORDINATOR2: [COORDINATOR2]int, 
    Civl_PAs_PARTICIPANT1: [PARTICIPANT1]int, 
    Civl_PAs_PARTICIPANT2: [PARTICIPANT2]int, 
    Civl_choice: Choice_INV2)
{
  var Civl_newPAs_PARTICIPANT2: [PARTICIPANT2]int;

  ISL_step_INV2_PARTICIPANT1:
    call Civl_PAs_COORDINATOR2, Civl_PAs_PARTICIPANT1, Civl_PAs_PARTICIPANT2, Civl_choice := INV2_With_Choice(pids);
    assume Civl_choice is Choice_INV2_PARTICIPANT1;
    assume Civl_PAs_PARTICIPANT1[Civl_choice->PARTICIPANT1] > 0;
    Civl_PAs_PARTICIPANT1[Civl_choice->PARTICIPANT1] := Civl_PAs_PARTICIPANT1[Civl_choice->PARTICIPANT1] - 1;
    assert pid(Civl_choice->PARTICIPANT1->pid->val);
    call Civl_newPAs_PARTICIPANT2 := PARTICIPANT1(Civl_choice->PARTICIPANT1->pid);
    Civl_PAs_PARTICIPANT2 := MapAdd_14175(Civl_PAs_PARTICIPANT2, Civl_newPAs_PARTICIPANT2);
    assert (exists {:pool "INV2"} Civl_k#0: int :: 
      0 <= Civl_k#0
         && Civl_k#0 <= n
         && (forall i: int :: pidGt(i, Civl_k#0) ==> RequestChannel[i] == 1)
         && VoteChannel[YES()] >= 0
         && VoteChannel[NO()] >= 0
         && VoteChannel[YES()] + VoteChannel[NO()] <= Civl_k#0
         && (VoteChannel[YES()] == Civl_k#0
           ==> (forall i: int :: pidLe(i, Civl_k#0) ==> votes[i] == YES()))
         && Civl_PAs_COORDINATOR2
           == MapAdd_14233(MapConst_3_14244(0), MapConst_3_14244(0)[COORDINATOR2(One_43(0)) := 1])
         && Civl_PAs_PARTICIPANT2
           == MapAdd_14175(MapConst_3_14186(0), 
            MapIte_14193_3((lambda pa: PARTICIPANT2 :: pidLe(pa->pid->val, Civl_k#0)), 
              MapConst_3_14186(1), 
              MapConst_3_14186(0)))
         && Civl_PAs_PARTICIPANT1
           == MapAdd_14143(MapConst_3_14154(0), 
            MapIte_14161_3((lambda {:pool "PARTICIPANT1"} pa: PARTICIPANT1 :: 
                pidGt(pa->pid->val, Civl_k#0)), 
              MapConst_3_14154(1), 
              MapConst_3_14154(0))));
    return;
}



implementation MAIN1_RefinementCheck(pids: Set_230)
   returns (Civl_PAs_COORDINATOR2: [COORDINATOR2]int, 
    Civl_PAs_PARTICIPANT1: [PARTICIPANT1]int)
{
  var pids': Set_230;
  var pid: One_43;
  var participantPids: Set_230;
  var inline$COORDINATOR1_RefinementCheck$0$pid: One_43;
  var inline$COORDINATOR1_RefinementCheck$0$RequestChannel: [int]int;

  /*** structured program:
    assert Init(pids->val, RequestChannel, VoteChannel, DecisionChannel, decisions);
    pids' := pids;
    call pid := One_Get_687(pids', 0);
    async call COORDINATOR1(pid);
    call participantPids := Set_Get_335(pids', (lambda i: int :: pid(i)));
    call {:linear participantPids} create_asyncs_4825((lambda pa: PARTICIPANT1 :: pid(pa->pid->val)));
  **** end structured program */

  anon0:
    Civl_PAs_COORDINATOR2, Civl_PAs_PARTICIPANT1 := MapConst_3_14244(0), MapConst_3_14154(0);
    assert Init(pids->val, RequestChannel, VoteChannel, DecisionChannel, decisions);
    pids' := pids;
    assert Set_Contains_43(pids', 0);
    pids' := Set_Remove_687(pids', 0);
    pid := One_43(0);
    goto inline$COORDINATOR1_RefinementCheck$0$Entry;

  inline$COORDINATOR1_RefinementCheck$0$Entry:
    inline$COORDINATOR1_RefinementCheck$0$pid := pid;
    inline$COORDINATOR1_RefinementCheck$0$RequestChannel := RequestChannel;
    goto inline$COORDINATOR1_RefinementCheck$0$anon0;

  inline$COORDINATOR1_RefinementCheck$0$anon0:
    assert inline$COORDINATOR1_RefinementCheck$0$pid->val == 0;
    RequestChannel := (lambda inline$COORDINATOR1_RefinementCheck$0$i: int :: 
      (if pid(inline$COORDINATOR1_RefinementCheck$0$i)
         then RequestChannel[inline$COORDINATOR1_RefinementCheck$0$i] + 1
         else RequestChannel[inline$COORDINATOR1_RefinementCheck$0$i]));
    Civl_PAs_COORDINATOR2 := MapAdd_14233(Civl_PAs_COORDINATOR2, 
      MapConst_3_14244(0)[COORDINATOR2(inline$COORDINATOR1_RefinementCheck$0$pid) := 1]);
    goto inline$COORDINATOR1_RefinementCheck$0$Return;

  inline$COORDINATOR1_RefinementCheck$0$Return:
    goto anon0$1;

  anon0$1:
    participantPids := Set_230((lambda i: int :: pid(i)));
    assert Set_IsSubset_335(participantPids, pids');
    pids' := Set_Difference_335(pids', participantPids);
    assert (forall Civl_pa: PARTICIPANT1 :: 
      (lambda pa: PARTICIPANT1 :: pid(pa->pid->val))[Civl_pa]
         ==> Set_Contains_43(participantPids, Civl_pa->pid->val));
    assert (forall Civl_pa1: PARTICIPANT1, Civl_pa2: PARTICIPANT1 :: 
      (lambda pa: PARTICIPANT1 :: pid(pa->pid->val))[Civl_pa1]
           && (lambda pa: PARTICIPANT1 :: pid(pa->pid->val))[Civl_pa2]
           && Civl_pa1 != Civl_pa2
         ==> Civl_pa1->pid != Civl_pa2->pid);
    Civl_PAs_PARTICIPANT1 := MapAdd_14143(Civl_PAs_PARTICIPANT1, 
      MapIte_14161_3((lambda pa: PARTICIPANT1 :: pid(pa->pid->val)), 
        MapConst_3_14154(1), 
        MapConst_3_14154(0)));
    return;
}



procedure MAIN1_RefinementCheck(pids: Set_230)
   returns (Civl_PAs_COORDINATOR2: [COORDINATOR2]int, 
    Civl_PAs_PARTICIPANT1: [PARTICIPANT1]int);
  requires true
     ==> (forall Civl_pa1: PARTICIPANT1, Civl_pa2: PARTICIPANT1 :: 
      (lambda pa: PARTICIPANT1 :: pid(pa->pid->val))[Civl_pa1]
           && (lambda pa: PARTICIPANT1 :: pid(pa->pid->val))[Civl_pa2]
           && Civl_pa1 != Civl_pa2
         ==> Civl_pa1->pid != Civl_pa2->pid);
  requires true
     ==> (forall Civl_pa: PARTICIPANT1 :: 
      (lambda pa: PARTICIPANT1 :: pid(pa->pid->val))[Civl_pa]
         ==> Set_Contains_43(Set_230((lambda i: int :: pid(i))), Civl_pa->pid->val));
  requires true
     ==> Set_IsSubset_335(Set_230((lambda i: int :: pid(i))), Set_Remove_687(pids, 0));
  requires true ==> Set_Contains_43(pids, 0);
  requires Init(pids->val, RequestChannel, VoteChannel, DecisionChannel, decisions);
  modifies RequestChannel;
  ensures true
     && RequestChannel == (lambda i: int :: (if pid(i) then 1 else 0))
     && Civl_PAs_COORDINATOR2
       == MapAdd_14233(MapConst_3_14244(0), MapConst_3_14244(0)[COORDINATOR2(One_43(0)) := 1])
     && Civl_PAs_PARTICIPANT1
       == MapAdd_14143(MapConst_3_14154(0), 
        MapIte_14161_3((lambda pa: PARTICIPANT1 :: pid(pa->pid->val)), 
          MapConst_3_14154(1), 
          MapConst_3_14154(0)))
     && DecisionChannel == old(DecisionChannel)
     && VoteChannel == old(VoteChannel)
     && votes == old(votes)
     && decisions == old(decisions);


