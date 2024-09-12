// Boogie program verifier version 3.2.2.0, Copyright (c) 2003-2014, Microsoft.
// Command Line Options: Easy-PC2.bpl /civlDesugaredFile:epc-sugar.bpl

type Pid = int;

type Cid = int;

type Duration = int;

datatype Vote {
  YES(),
  NO(),
  NULL()
}

datatype Decision {
  COMMIT(),
  ABORT(),
  NONE()
}

type ReqId;

datatype Request {
  Request(id: ReqId, duration: int)
}

const n: int;

var locked_requests: [int]Set_3804;

var participant_votes: [int][Request]Vote;

var committed_requests: Set_3804;

function {:inline} Init(participant_votes: [int][Request]Vote) : bool
{
  participant_votes == (lambda p: int :: (lambda r: Request :: NULL()))
}

function {:inline} NoOverlap(req_set: Set_3804, d: int) : bool
{
  !(exists req: Request :: Set_Contains_3047(req_set, req) && req->duration == d)
}

datatype skip {
  skip(req: Request)
}

datatype MAIN_F' {
  MAIN_F'(req: Request)
}

datatype MAIN_F {
  MAIN_F(req: Request)
}

datatype voting {
  voting(req: Request, pid: One_15)
}

const Identity: [int]int;

function {:inline} AtLeast(x: int) : [int]bool
{
  MapLe_1195(MapConst_1212_1195(x), Identity)
}

function {:inline} Range(from: int, n: int) : [int]bool
{
  MapDiff_1215(AtLeast(from), AtLeast(from + n))
}

type {:builtin "Seq"} Seq _;

pure procedure Assume(b: bool);
  ensures b;



datatype Set_3804 {
  Set_3804(val: [Request]bool)
}

function {:inline} Set_Contains_3047(a: Set_3804, t: Request) : bool
{
  a->val[t]
}

datatype One_15 {
  One_15(val: int)
}

procedure create_asyncs_3062(PAs: [voting]bool);



procedure set_choice_3068(choice: voting);



function {:inline} Set_Add_3038(a: Set_3804, t: Request) : Set_3804
{
  Set_3804(a->val[t := true])
}

function {:builtin "MapConst"} MapConst_1212_1195(int) : [int]int;

function {:builtin "MapLe"} MapLe_1195([int]int, [int]int) : [int]bool;

function {:inline} MapDiff_1215(a: [int]bool, b: [int]bool) : [int]bool
{
  MapAnd_1215(a, MapNot_1215(b))
}

function {:builtin "MapNot"} MapNot_1215([int]bool) : [int]bool;

function {:builtin "MapAnd"} MapAnd_1215([int]bool, [int]bool) : [int]bool;

datatype Vec_1212 {
  Vec_1212(contents: [int]int, len: int)
}

function Default_1212() : int;

function {:builtin "MapIte"} MapIte_1236_1212([int]bool, [int]int, [int]int) : [int]int;

function {:builtin "MapConst"} MapConst_5_1195(bool) : [int]bool;

function Choice_1195(a: [int]bool) : int;

datatype Vec_5 {
  Vec_5(contents: [int]bool, len: int)
}

function Default_5() : bool;

function {:builtin "MapIte"} MapIte_1236_5([int]bool, [int]bool, [int]bool) : [int]bool;

axiom n > 0;

axiom (forall x: int :: Identity[x] == x);

axiom (forall x: Vec_5 :: 
  { x->len } { x->contents } 
  MapIte_1236_5(Range(0, x->len), MapConst_5_1195(Default_5()), x->contents)
     == MapConst_5_1195(Default_5()));

axiom (forall x: Vec_1212 :: 
  { x->len } { x->contents } 
  MapIte_1236_1212(Range(0, x->len), MapConst_1212_1195(Default_1212()), x->contents)
     == MapConst_1212_1195(Default_1212()));

axiom (forall x: Vec_5 :: { x->len } x->len >= 0);

axiom (forall x: Vec_1212 :: { x->len } x->len >= 0);

axiom (forall a: [int]bool :: 
  { Choice_1195(a) } 
  a == MapConst_5_1195(false) || a[Choice_1195(a)]);

function {:builtin "MapConst"} MapConst_5_3804(bool) : [Request]bool;

function {:builtin "MapConst"} MapConst_3_3804(int) : [Request]int;

function {:builtin "MapAnd"} MapAnd_3804([Request]bool, [Request]bool) : [Request]bool;

function {:builtin "MapOr"} MapOr_3804([Request]bool, [Request]bool) : [Request]bool;

function {:builtin "MapImp"} MapImp_3804([Request]bool, [Request]bool) : [Request]bool;

function {:builtin "MapEq"} MapEq_3804_3([Request]int, [Request]int) : [Request]bool;

function {:builtin "MapAdd"} MapAdd_3804([Request]int, [Request]int) : [Request]int;

function {:builtin "MapIte"} MapIte_3804_3([Request]bool, [Request]int, [Request]int) : [Request]int;

function {:builtin "MapLe"} MapLe_3804([Request]int, [Request]int) : [Request]bool;

function {:inline} Set_Collector_3804(a: Set_3804) : [Request]bool
{
  a->val
}

function {:builtin "MapOr"} MapOr_15([int]bool, [int]bool) : [int]bool;

function {:builtin "MapImp"} MapImp_15([int]bool, [int]bool) : [int]bool;

function {:builtin "MapEq"} MapEq_15_3([int]int, [int]int) : [int]bool;

function {:builtin "MapAdd"} MapAdd_15([int]int, [int]int) : [int]int;

function {:inline} One_Collector_15(a: One_15) : [int]bool
{
  MapOne_15(a->val)
}

function {:inline} MapOne_15(t: int) : [int]bool
{
  MapConst_5_1195(false)[t := true]
}

function {:inline} Collector_voting_int(target: voting) : [int]bool
{
  (if target is voting
     then MapOr_15(One_Collector_15(target->pid), MapConst_5_1195(false))
     else MapConst_5_1195(false))
}

function {:builtin "MapAdd"} MapAdd_6351([skip]int, [skip]int) : [skip]int;

function {:builtin "MapConst"} MapConst_3_6362(int) : [skip]int;

function {:builtin "MapIte"} MapIte_6369_3([skip]bool, [skip]int, [skip]int) : [skip]int;

function {:builtin "MapAdd"} MapAdd_6383([MAIN_F']int, [MAIN_F']int) : [MAIN_F']int;

function {:builtin "MapConst"} MapConst_3_6394(int) : [MAIN_F']int;

function {:builtin "MapIte"} MapIte_6401_3([MAIN_F']bool, [MAIN_F']int, [MAIN_F']int) : [MAIN_F']int;

function {:builtin "MapAdd"} MapAdd_6415([MAIN_F]int, [MAIN_F]int) : [MAIN_F]int;

function {:builtin "MapConst"} MapConst_3_6426(int) : [MAIN_F]int;

function {:builtin "MapIte"} MapIte_6433_3([MAIN_F]bool, [MAIN_F]int, [MAIN_F]int) : [MAIN_F]int;

function {:builtin "MapAdd"} MapAdd_6447([voting]int, [voting]int) : [voting]int;

function {:builtin "MapConst"} MapConst_3_6458(int) : [voting]int;

function {:builtin "MapIte"} MapIte_6465_3([voting]bool, [voting]int, [voting]int) : [voting]int;

datatype Choice_Inv {
  Choice_Inv_voting(voting: voting)
}

function Trigger_Inv_j(j: int) : bool;

function Trigger_Inv_choice(choice: voting) : bool;

implementation skip(req: Request)
{
  /*** structured program:
  **** end structured program */

  anon0:
    return;
}



procedure {:inline 1} skip(req: Request);



function {:inline} Civl_InputOutputRelation_skip(req: Request) : bool
{
  (exists Civl_old_locked_requests: [int]Set_3804, 
      Civl_old_participant_votes: [int][Request]Vote, 
      Civl_old_committed_requests: Set_3804, 
      Civl_locked_requests: [int]Set_3804, 
      Civl_participant_votes: [int][Request]Vote, 
      Civl_committed_requests: Set_3804 :: 
    true)
}

implementation MAIN_F'(req: Request)
{
  /*** structured program:
    assume (forall p: int :: 
      1 <= p && p <= n
         ==> participant_votes[p][req] == YES() || participant_votes[p][req] == NO());
    assume (forall p: int :: 
      participant_votes[p][req] == YES()
         <==> Set_Contains_3047(locked_requests[p], req));
  **** end structured program */

  anon0:
    assume (forall p: int :: 
      1 <= p && p <= n
         ==> participant_votes[p][req] == YES() || participant_votes[p][req] == NO());
    assume (forall p: int :: 
      participant_votes[p][req] == YES()
         <==> Set_Contains_3047(locked_requests[p], req));
    return;
}



procedure {:inline 1} MAIN_F'(req: Request);



function {:inline} Civl_InputOutputRelation_MAIN_F'(req: Request) : bool
{
  (exists Civl_old_locked_requests: [int]Set_3804, 
      Civl_old_participant_votes: [int][Request]Vote, 
      Civl_old_committed_requests: Set_3804, 
      Civl_locked_requests: [int]Set_3804, 
      Civl_participant_votes: [int][Request]Vote, 
      Civl_committed_requests: Set_3804 :: 
    (forall p: int :: 
        1 <= p && p <= n
           ==> Civl_participant_votes[p][req] == YES()
             || Civl_participant_votes[p][req] == NO())
       && (forall p: int :: 
        Civl_participant_votes[p][req] == YES()
           <==> Set_Contains_3047(Civl_locked_requests[p], req)))
}

implementation Inv(req: Request) returns (Civl_PAs_voting: [voting]int)
{
  var {:pool "A"} j: int;
  var choice: voting;

  /*** structured program:
    assume {:add_to_pool "A", 0, j + 1, n} 0 <= j && j <= n;
    assume (forall i: int :: 
      1 <= i && i <= j
         ==> participant_votes[i][req] == YES() || participant_votes[i][req] == YES());
    assume (forall i: int :: 
      1 <= i && i <= j
         ==> (participant_votes[i][req] == YES()
           <==> Set_Contains_3047(locked_requests[i], req)));
    if (j < n)
    {
        choice := voting(req, One_15(j + 1));
        call create_asyncs((lambda {:pool "C"} pa: voting :: 
          j + 1 <= pa->pid->val && pa->pid->val <= n && pa->req == req));
        call set_choice(choice);
    }
  **** end structured program */

  anon0:
    assume Trigger_Inv_j(j);
    Civl_PAs_voting := MapConst_3_6458(0);
    assume {:add_to_pool "A", 0, j + 1, n} 0 <= j && j <= n;
    assume (forall i: int :: 
      1 <= i && i <= j
         ==> participant_votes[i][req] == YES() || participant_votes[i][req] == YES());
    assume (forall i: int :: 
      1 <= i && i <= j
         ==> (participant_votes[i][req] == YES()
           <==> Set_Contains_3047(locked_requests[i], req)));
    goto anon2_Then, anon2_Else;

  anon2_Else:
    assume {:partition} n <= j;
    return;

  anon2_Then:
    assume {:partition} j < n;
    choice := voting(req, One_15(j + 1));
    Civl_PAs_voting := MapAdd_6447(Civl_PAs_voting, 
      MapIte_6465_3((lambda {:pool "C"} pa: voting :: 
          j + 1 <= pa->pid->val && pa->pid->val <= n && pa->req == req), 
        MapConst_3_6458(1), 
        MapConst_3_6458(0)));
    return;
}



procedure {:inline 1} Inv(req: Request) returns (Civl_PAs_voting: [voting]int);
  modifies participant_votes, locked_requests;



function {:inline} Civl_InputOutputRelation_Inv(req: Request, Civl_PAs_voting: [voting]int) : bool
{
  (exists Civl_old_locked_requests: [int]Set_3804, 
      Civl_old_participant_votes: [int][Request]Vote, 
      Civl_old_committed_requests: Set_3804, 
      Civl_locked_requests: [int]Set_3804, 
      Civl_participant_votes: [int][Request]Vote, 
      Civl_committed_requests: Set_3804 :: 
    (exists {:pool "A"} Civl_j#0: int :: 
        0 <= Civl_j#0
           && Civl_j#0 <= n
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0
               ==> Civl_participant_votes[i][req] == YES()
                 || Civl_participant_votes[i][req] == YES())
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0
               ==> (Civl_participant_votes[i][req] == YES()
                 <==> Set_Contains_3047(Civl_locked_requests[i], req)))
           && Civl_j#0 < n
           && Civl_PAs_voting
             == MapAdd_6447(MapConst_3_6458(0), 
              MapIte_6465_3((lambda {:pool "C"} pa: voting :: 
                  Civl_j#0 + 1 <= pa->pid->val && pa->pid->val <= n && pa->req == req), 
                MapConst_3_6458(1), 
                MapConst_3_6458(0)))
           && Civl_participant_votes == Civl_old_participant_votes
           && Civl_locked_requests == Civl_old_locked_requests)
       || (exists {:pool "A"} Civl_j#0: int :: 
        0 <= Civl_j#0
           && Civl_j#0 <= n
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0
               ==> Civl_participant_votes[i][req] == YES()
                 || Civl_participant_votes[i][req] == YES())
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0
               ==> (Civl_participant_votes[i][req] == YES()
                 <==> Set_Contains_3047(Civl_locked_requests[i], req)))
           && n <= Civl_j#0
           && Civl_PAs_voting == MapConst_3_6458(0)
           && Civl_participant_votes == Civl_old_participant_votes
           && Civl_locked_requests == Civl_old_locked_requests))
}

implementation Inv_With_Choice(req: Request) returns (Civl_PAs_voting: [voting]int, Civl_choice: Choice_Inv)
{
  var {:pool "A"} j: int;
  var choice: voting;

  /*** structured program:
    assume {:add_to_pool "A", 0, j + 1, n} 0 <= j && j <= n;
    assume (forall i: int :: 
      1 <= i && i <= j
         ==> participant_votes[i][req] == YES() || participant_votes[i][req] == YES());
    assume (forall i: int :: 
      1 <= i && i <= j
         ==> (participant_votes[i][req] == YES()
           <==> Set_Contains_3047(locked_requests[i], req)));
    if (j < n)
    {
        choice := voting(req, One_15(j + 1));
        call create_asyncs((lambda {:pool "C"} pa: voting :: 
          j + 1 <= pa->pid->val && pa->pid->val <= n && pa->req == req));
        call set_choice(choice);
    }
  **** end structured program */

  anon0:
    Civl_PAs_voting := MapConst_3_6458(0);
    assume {:add_to_pool "A", 0, j + 1, n} 0 <= j && j <= n;
    assume (forall i: int :: 
      1 <= i && i <= j
         ==> participant_votes[i][req] == YES() || participant_votes[i][req] == YES());
    assume (forall i: int :: 
      1 <= i && i <= j
         ==> (participant_votes[i][req] == YES()
           <==> Set_Contains_3047(locked_requests[i], req)));
    goto anon2_Then, anon2_Else;

  anon2_Else:
    assume {:partition} n <= j;
    return;

  anon2_Then:
    assume {:partition} j < n;
    choice := voting(req, One_15(j + 1));
    Civl_PAs_voting := MapAdd_6447(Civl_PAs_voting, 
      MapIte_6465_3((lambda {:pool "C"} pa: voting :: 
          j + 1 <= pa->pid->val && pa->pid->val <= n && pa->req == req), 
        MapConst_3_6458(1), 
        MapConst_3_6458(0)));
    assert Civl_PAs_voting == MapConst_3_6458(0) || Civl_PAs_voting[choice] > 0;
    Civl_choice->voting := choice;
    return;
}



procedure {:inline 1} Inv_With_Choice(req: Request) returns (Civl_PAs_voting: [voting]int, Civl_choice: Choice_Inv);
  modifies participant_votes, locked_requests;



function {:inline} Civl_InputOutputRelation_Inv_With_Choice(req: Request, Civl_PAs_voting: [voting]int, Civl_choice: Choice_Inv) : bool
{
  (exists Civl_old_locked_requests: [int]Set_3804, 
      Civl_old_participant_votes: [int][Request]Vote, 
      Civl_old_committed_requests: Set_3804, 
      Civl_locked_requests: [int]Set_3804, 
      Civl_participant_votes: [int][Request]Vote, 
      Civl_committed_requests: Set_3804 :: 
    (exists {:pool "A"} Civl_j#0: int :: 
        0 <= Civl_j#0
           && Civl_j#0 <= n
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0
               ==> Civl_participant_votes[i][req] == YES()
                 || Civl_participant_votes[i][req] == YES())
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0
               ==> (Civl_participant_votes[i][req] == YES()
                 <==> Set_Contains_3047(Civl_locked_requests[i], req)))
           && Civl_j#0 < n
           && (Civl_PAs_voting == MapConst_3_6458(0)
             || Civl_PAs_voting[voting(req, One_15(Civl_j#0 + 1))] > 0)
           && Civl_PAs_voting
             == MapAdd_6447(MapConst_3_6458(0), 
              MapIte_6465_3((lambda {:pool "C"} pa: voting :: 
                  Civl_j#0 + 1 <= pa->pid->val && pa->pid->val <= n && pa->req == req), 
                MapConst_3_6458(1), 
                MapConst_3_6458(0)))
           && Civl_choice == Choice_Inv_voting(voting(req, One_15(Civl_j#0 + 1)))
           && Civl_participant_votes == Civl_old_participant_votes
           && Civl_locked_requests == Civl_old_locked_requests)
       || (exists {:pool "A"} Civl_j#0: int :: 
        0 <= Civl_j#0
           && Civl_j#0 <= n
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0
               ==> Civl_participant_votes[i][req] == YES()
                 || Civl_participant_votes[i][req] == YES())
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0
               ==> (Civl_participant_votes[i][req] == YES()
                 <==> Set_Contains_3047(Civl_locked_requests[i], req)))
           && n <= Civl_j#0
           && Civl_PAs_voting == MapConst_3_6458(0)
           && Civl_participant_votes == Civl_old_participant_votes
           && Civl_locked_requests == Civl_old_locked_requests))
}

implementation ADD_TO_COMMITTED_REQUESTS(req: Request)
{
  /*** structured program:
    committed_requests := Set_Add_3038(committed_requests, req);
  **** end structured program */

  anon0:
    committed_requests := Set_Add_3038(committed_requests, req);
    return;
}



procedure {:inline 1} ADD_TO_COMMITTED_REQUESTS(req: Request);
  modifies committed_requests;



function {:inline} Civl_InputOutputRelation_ADD_TO_COMMITTED_REQUESTS(req: Request) : bool
{
  (exists Civl_old_locked_requests: [int]Set_3804, 
      Civl_old_participant_votes: [int][Request]Vote, 
      Civl_old_committed_requests: Set_3804, 
      Civl_locked_requests: [int]Set_3804, 
      Civl_participant_votes: [int][Request]Vote, 
      Civl_committed_requests: Set_3804 :: 
    Civl_committed_requests == Set_Add_3038(Civl_old_committed_requests, req))
}

implementation RECEIVE_VOTE(pid: One_15, req: Request) returns (v: Vote)
{
  /*** structured program:
    v := participant_votes[pid->val][req];
  **** end structured program */

  anon0:
    v := participant_votes[pid->val][req];
    return;
}



procedure {:inline 1} RECEIVE_VOTE(pid: One_15, req: Request) returns (v: Vote);



function {:inline} Civl_InputOutputRelation_RECEIVE_VOTE(pid: One_15, req: Request, v: Vote) : bool
{
  (exists Civl_old_locked_requests: [int]Set_3804, 
      Civl_old_participant_votes: [int][Request]Vote, 
      Civl_old_committed_requests: Set_3804, 
      Civl_locked_requests: [int]Set_3804, 
      Civl_participant_votes: [int][Request]Vote, 
      Civl_committed_requests: Set_3804 :: 
    v == Civl_participant_votes[pid->val][req])
}

implementation WAIT_FOR_PARTICIPANT_VOTE(req: Request)
{
  /*** structured program:
    assume (forall pid: int :: 
      1 <= pid && pid <= n ==> participant_votes[pid][req] != NULL());
  **** end structured program */

  anon0:
    assume (forall pid: int :: 
      1 <= pid && pid <= n ==> participant_votes[pid][req] != NULL());
    return;
}



procedure {:inline 1} WAIT_FOR_PARTICIPANT_VOTE(req: Request);



function {:inline} Civl_InputOutputRelation_WAIT_FOR_PARTICIPANT_VOTE(req: Request) : bool
{
  (exists Civl_old_locked_requests: [int]Set_3804, 
      Civl_old_participant_votes: [int][Request]Vote, 
      Civl_old_committed_requests: Set_3804, 
      Civl_locked_requests: [int]Set_3804, 
      Civl_participant_votes: [int][Request]Vote, 
      Civl_committed_requests: Set_3804 :: 
    (forall pid: int :: 
      1 <= pid && pid <= n ==> Civl_participant_votes[pid][req] != NULL()))
}

implementation voting(req: Request, pid: One_15)
{
  /*** structured program:
    assert !(exists req0: Request :: 
      Set_Contains_3047(locked_requests[pid->val], req0) && req0->id == req->id);
    if (*)
    {
        participant_votes[pid->val][req] := NO();
        return;
    }
    else
    {
        if (NoOverlap(locked_requests[pid->val], req->duration))
        {
            locked_requests[pid->val] := Set_Add_3038(locked_requests[pid->val], req);
            participant_votes[pid->val][req] := YES();
        }
        else
        {
            participant_votes[pid->val][req] := NO();
        }
    }
  **** end structured program */

  anon0:
    goto anon5_Then, anon5_Else;

  anon5_Else:
    goto anon6_Then, anon6_Else;

  anon6_Else:
    assume {:partition} !NoOverlap(locked_requests[pid->val], req->duration);
    participant_votes[pid->val][req] := NO();
    return;

  anon6_Then:
    assume {:partition} NoOverlap(locked_requests[pid->val], req->duration);
    locked_requests[pid->val] := Set_Add_3038(locked_requests[pid->val], req);
    participant_votes[pid->val][req] := YES();
    return;

  anon5_Then:
    participant_votes[pid->val][req] := NO();
    return;
}



procedure {:inline 1} voting(req: Request, pid: One_15);
  modifies locked_requests, participant_votes;



function {:inline} Civl_InputOutputRelation_voting(req: Request, pid: One_15) : bool
{
  (exists Civl_old_locked_requests: [int]Set_3804, 
      Civl_old_participant_votes: [int][Request]Vote, 
      Civl_old_committed_requests: Set_3804, 
      Civl_locked_requests: [int]Set_3804, 
      Civl_participant_votes: [int][Request]Vote, 
      Civl_committed_requests: Set_3804 :: 
    !(exists req0: Request :: 
        Set_Contains_3047(Civl_old_locked_requests[pid->val], req0)
           && req0->id == req->id)
       && (
        (Civl_participant_votes
             == Civl_old_participant_votes[pid->val := Civl_old_participant_votes[pid->val][req := NO()]]
           && Civl_locked_requests == Civl_old_locked_requests)
         || (
          NoOverlap(Civl_old_locked_requests[pid->val], req->duration)
           && Civl_locked_requests
             == Civl_old_locked_requests[pid->val := Set_Add_3038(Civl_old_locked_requests[pid->val], req)]
           && Civl_participant_votes
             == Civl_old_participant_votes[pid->val := Civl_old_participant_votes[pid->val][req := YES()]])
         || (
          !NoOverlap(Civl_locked_requests[pid->val], req->duration)
           && Civl_participant_votes
             == Civl_old_participant_votes[pid->val := Civl_old_participant_votes[pid->val][req := NO()]]
           && Civl_locked_requests == Civl_old_locked_requests)))
}

implementation Civl_Skip()
{

  init:
    return;
}



pure procedure {:inline 1} Civl_Skip();



function {:inline} Civl_InputOutputRelation_Civl_Skip() : bool
{
  (exists Civl_old_locked_requests: [int]Set_3804, 
      Civl_old_participant_votes: [int][Request]Vote, 
      Civl_old_committed_requests: Set_3804, 
      Civl_locked_requests: [int]Set_3804, 
      Civl_participant_votes: [int][Request]Vote, 
      Civl_committed_requests: Set_3804 :: 
    true)
}

implementation MAIN_F(req: Request) returns (Civl_PAs_voting: [voting]int)
{
  /*** structured program:
    call create_asyncs_3062((lambda pa: voting :: pa->req == req && pa->pid->val >= 1 && pa->pid->val <= n));
  **** end structured program */

  anon0:
    Civl_PAs_voting := MapConst_3_6458(0);
    Civl_PAs_voting := MapAdd_6447(Civl_PAs_voting, 
      MapIte_6465_3((lambda pa: voting :: pa->req == req && pa->pid->val >= 1 && pa->pid->val <= n), 
        MapConst_3_6458(1), 
        MapConst_3_6458(0)));
    return;
}



procedure {:inline 1} MAIN_F(req: Request) returns (Civl_PAs_voting: [voting]int);



function {:inline} Civl_InputOutputRelation_MAIN_F(req: Request, Civl_PAs_voting: [voting]int) : bool
{
  (exists Civl_old_locked_requests: [int]Set_3804, 
      Civl_old_participant_votes: [int][Request]Vote, 
      Civl_old_committed_requests: Set_3804, 
      Civl_locked_requests: [int]Set_3804, 
      Civl_participant_votes: [int][Request]Vote, 
      Civl_committed_requests: Set_3804 :: 
    Civl_PAs_voting
       == MapAdd_6447(MapConst_3_6458(0), 
        MapIte_6465_3((lambda pa: voting :: pa->req == req && pa->pid->val >= 1 && pa->pid->val <= n), 
          MapConst_3_6458(1), 
          MapConst_3_6458(0))))
}

implementation Civl_CommutativityChecker_voting_RECEIVE_VOTE_1(first_req: Request, first_pid: One_15, second_pid: One_15, second_req: Request)
   returns (second_v: Vote)
{

  init:
    call voting(first_req, first_pid);
    call second_v := RECEIVE_VOTE(second_pid, second_req);
    assert true
       ==> (
          second_v == old(participant_votes)[second_pid->val][second_req]
           && participant_votes
             == old(participant_votes)[first_pid->val := old(participant_votes)[first_pid->val][first_req := NO()]]
           && locked_requests == old(locked_requests))
         || (
          NoOverlap(old(locked_requests)[first_pid->val], first_req->duration)
           && second_v == old(participant_votes)[second_pid->val][second_req]
           && locked_requests
             == old(locked_requests)[first_pid->val := Set_Add_3038(old(locked_requests)[first_pid->val], first_req)]
           && participant_votes
             == old(participant_votes)[first_pid->val := old(participant_votes)[first_pid->val][first_req := YES()]])
         || (
          !NoOverlap(locked_requests[first_pid->val], first_req->duration)
           && second_v == old(participant_votes)[second_pid->val][second_req]
           && participant_votes
             == old(participant_votes)[first_pid->val := old(participant_votes)[first_pid->val][first_req := NO()]]
           && locked_requests == old(locked_requests));
    return;
}



procedure Civl_CommutativityChecker_voting_RECEIVE_VOTE_1(first_req: Request, first_pid: One_15, second_pid: One_15, second_req: Request)
   returns (second_v: Vote);
  requires true;
  requires (exists Civl_partition_int: [int]int :: 
    MapImp_15(One_Collector_15(first_pid), 
          MapEq_15_3(Civl_partition_int, MapConst_1212_1195(0)))
         == MapConst_5_1195(true)
       && MapImp_15(One_Collector_15(second_pid), 
          MapEq_15_3(Civl_partition_int, MapConst_1212_1195(1)))
         == MapConst_5_1195(true));
  requires !(exists first_req0: Request :: 
    Set_Contains_3047(locked_requests[first_pid->val], first_req0)
       && first_req0->id == first_req->id);
  requires !false;
  modifies locked_requests, participant_votes, committed_requests;



implementation Civl_CommutativityChecker_voting_WAIT_FOR_PARTICIPANT_VOTE_1(first_req: Request, first_pid: One_15, second_req: Request)
{

  init:
    call voting(first_req, first_pid);
    call WAIT_FOR_PARTICIPANT_VOTE(second_req);
    assert true
       ==> (
          (forall second_pid: int :: 
            1 <= second_pid && second_pid <= n
               ==> old(participant_votes)[second_pid][second_req] != NULL())
           && participant_votes
             == old(participant_votes)[first_pid->val := old(participant_votes)[first_pid->val][first_req := NO()]]
           && locked_requests == old(locked_requests))
         || (
          (forall second_pid: int :: 
            1 <= second_pid && second_pid <= n
               ==> old(participant_votes)[second_pid][second_req] != NULL())
           && NoOverlap(old(locked_requests)[first_pid->val], first_req->duration)
           && locked_requests
             == old(locked_requests)[first_pid->val := Set_Add_3038(old(locked_requests)[first_pid->val], first_req)]
           && participant_votes
             == old(participant_votes)[first_pid->val := old(participant_votes)[first_pid->val][first_req := YES()]])
         || (
          (forall second_pid: int :: 
            1 <= second_pid && second_pid <= n
               ==> old(participant_votes)[second_pid][second_req] != NULL())
           && !NoOverlap(locked_requests[first_pid->val], first_req->duration)
           && participant_votes
             == old(participant_votes)[first_pid->val := old(participant_votes)[first_pid->val][first_req := NO()]]
           && locked_requests == old(locked_requests));
    return;
}



procedure Civl_CommutativityChecker_voting_WAIT_FOR_PARTICIPANT_VOTE_1(first_req: Request, first_pid: One_15, second_req: Request);
  requires true;
  requires !(exists first_req0: Request :: 
    Set_Contains_3047(locked_requests[first_pid->val], first_req0)
       && first_req0->id == first_req->id);
  requires !false;
  modifies locked_requests, participant_votes, committed_requests;



implementation Civl_CommutativityChecker_voting_voting_1(first_req: Request, first_pid: One_15, second_req: Request, second_pid: One_15)
{

  init:
    call voting(first_req, first_pid);
    call voting(second_req, second_pid);
    assert true
       ==> (participant_votes
             == old(participant_votes)[second_pid->val := old(participant_votes)[second_pid->val][second_req := NO()]][first_pid->val := old(participant_votes)[second_pid->val := old(participant_votes)[second_pid->val][second_req := NO()]][first_pid->val][first_req := NO()]]
           && locked_requests == old(locked_requests))
         || (
          NoOverlap(old(locked_requests)[first_pid->val], first_req->duration)
           && locked_requests
             == old(locked_requests)[first_pid->val := Set_Add_3038(old(locked_requests)[first_pid->val], first_req)]
           && participant_votes
             == old(participant_votes)[second_pid->val := old(participant_votes)[second_pid->val][second_req := NO()]][first_pid->val := old(participant_votes)[second_pid->val := old(participant_votes)[second_pid->val][second_req := NO()]][first_pid->val][first_req := YES()]])
         || (
          !NoOverlap(locked_requests[first_pid->val], first_req->duration)
           && participant_votes
             == old(participant_votes)[second_pid->val := old(participant_votes)[second_pid->val][second_req := NO()]][first_pid->val := old(participant_votes)[second_pid->val := old(participant_votes)[second_pid->val][second_req := NO()]][first_pid->val][first_req := NO()]]
           && locked_requests == old(locked_requests))
         || (
          NoOverlap(old(locked_requests)[second_pid->val], second_req->duration)
           && locked_requests
             == old(locked_requests)[second_pid->val := Set_Add_3038(old(locked_requests)[second_pid->val], second_req)]
           && participant_votes
             == old(participant_votes)[second_pid->val := old(participant_votes)[second_pid->val][second_req := YES()]][first_pid->val := old(participant_votes)[second_pid->val := old(participant_votes)[second_pid->val][second_req := YES()]][first_pid->val][first_req := NO()]])
         || (
          NoOverlap(old(locked_requests)[second_pid->val], second_req->duration)
           && NoOverlap(old(locked_requests)[second_pid->val := Set_Add_3038(old(locked_requests)[second_pid->val], second_req)][first_pid->val], 
            first_req->duration)
           && locked_requests
             == old(locked_requests)[second_pid->val := Set_Add_3038(old(locked_requests)[second_pid->val], second_req)][first_pid->val := Set_Add_3038(old(locked_requests)[second_pid->val := Set_Add_3038(old(locked_requests)[second_pid->val], second_req)][first_pid->val], 
              first_req)]
           && participant_votes
             == old(participant_votes)[second_pid->val := old(participant_votes)[second_pid->val][second_req := YES()]][first_pid->val := old(participant_votes)[second_pid->val := old(participant_votes)[second_pid->val][second_req := YES()]][first_pid->val][first_req := YES()]])
         || (
          NoOverlap(old(locked_requests)[second_pid->val], second_req->duration)
           && !NoOverlap(locked_requests[first_pid->val], first_req->duration)
           && locked_requests
             == old(locked_requests)[second_pid->val := Set_Add_3038(old(locked_requests)[second_pid->val], second_req)]
           && participant_votes
             == old(participant_votes)[second_pid->val := old(participant_votes)[second_pid->val][second_req := YES()]][first_pid->val := old(participant_votes)[second_pid->val := old(participant_votes)[second_pid->val][second_req := YES()]][first_pid->val][first_req := NO()]])
         || (
          !NoOverlap(locked_requests[second_pid->val], second_req->duration)
           && participant_votes
             == old(participant_votes)[second_pid->val := old(participant_votes)[second_pid->val][second_req := NO()]][first_pid->val := old(participant_votes)[second_pid->val := old(participant_votes)[second_pid->val][second_req := NO()]][first_pid->val][first_req := NO()]]
           && locked_requests == old(locked_requests))
         || (
          !NoOverlap(old(locked_requests)[second_pid->val], second_req->duration)
           && NoOverlap(old(locked_requests)[first_pid->val], first_req->duration)
           && locked_requests
             == old(locked_requests)[first_pid->val := Set_Add_3038(old(locked_requests)[first_pid->val], first_req)]
           && participant_votes
             == old(participant_votes)[second_pid->val := old(participant_votes)[second_pid->val][second_req := NO()]][first_pid->val := old(participant_votes)[second_pid->val := old(participant_votes)[second_pid->val][second_req := NO()]][first_pid->val][first_req := YES()]])
         || (
          !NoOverlap(locked_requests[second_pid->val], second_req->duration)
           && !NoOverlap(locked_requests[first_pid->val], first_req->duration)
           && participant_votes
             == old(participant_votes)[second_pid->val := old(participant_votes)[second_pid->val][second_req := NO()]][first_pid->val := old(participant_votes)[second_pid->val := old(participant_votes)[second_pid->val][second_req := NO()]][first_pid->val][first_req := NO()]]
           && locked_requests == old(locked_requests));
    return;
}



procedure Civl_CommutativityChecker_voting_voting_1(first_req: Request, first_pid: One_15, second_req: Request, second_pid: One_15);
  requires true;
  requires (exists Civl_partition_int: [int]int :: 
    MapImp_15(One_Collector_15(first_pid), 
          MapEq_15_3(Civl_partition_int, MapConst_1212_1195(0)))
         == MapConst_5_1195(true)
       && MapImp_15(One_Collector_15(second_pid), 
          MapEq_15_3(Civl_partition_int, MapConst_1212_1195(1)))
         == MapConst_5_1195(true));
  requires !(exists first_req0: Request :: 
    Set_Contains_3047(locked_requests[first_pid->val], first_req0)
       && first_req0->id == first_req->id);
  requires !(exists second_req0: Request :: 
    Set_Contains_3047(locked_requests[second_pid->val], second_req0)
       && second_req0->id == second_req->id);
  requires !false;
  modifies locked_requests, participant_votes, committed_requests;



implementation Civl_GatePreservationChecker_voting_voting_1(first_req: Request, first_pid: One_15, second_req: Request, second_pid: One_15)
{

  init:
    call voting(second_req, second_pid);
    assert true
       ==> !(exists first_req0: Request :: 
        Set_Contains_3047(locked_requests[first_pid->val], first_req0)
           && first_req0->id == first_req->id);
    return;
}



procedure Civl_GatePreservationChecker_voting_voting_1(first_req: Request, first_pid: One_15, second_req: Request, second_pid: One_15);
  requires true;
  requires (exists Civl_partition_int: [int]int :: 
    MapImp_15(One_Collector_15(first_pid), 
          MapEq_15_3(Civl_partition_int, MapConst_1212_1195(0)))
         == MapConst_5_1195(true)
       && MapImp_15(One_Collector_15(second_pid), 
          MapEq_15_3(Civl_partition_int, MapConst_1212_1195(1)))
         == MapConst_5_1195(true));
  requires !(exists first_req0: Request :: 
    Set_Contains_3047(locked_requests[first_pid->val], first_req0)
       && first_req0->id == first_req->id);
  requires !(exists second_req0: Request :: 
    Set_Contains_3047(locked_requests[second_pid->val], second_req0)
       && second_req0->id == second_req->id);
  requires !false;
  modifies locked_requests, participant_votes, committed_requests;



procedure {:inline 1} Civl_NoninterferenceChecker_yield_YieldTrue(Civl_linear_Request_in: [Request]bool, 
    Civl_linear_int_in: [int]bool, 
    Civl_snapshot_locked_requests: [int]Set_3804, 
    Civl_snapshot_participant_votes: [int][Request]Vote, 
    Civl_snapshot_committed_requests: Set_3804);



implementation Civl_NoninterferenceChecker_yield_YieldTrue(Civl_linear_Request_in: [Request]bool, 
    Civl_linear_int_in: [int]bool, 
    Civl_snapshot_locked_requests: [int]Set_3804, 
    Civl_snapshot_participant_votes: [int][Request]Vote, 
    Civl_snapshot_committed_requests: Set_3804)
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



procedure Civl_PendingAsyncNoninterferenceChecker_voting_1(req: Request, pid: One_15);
  requires !(exists req0: Request :: 
    Set_Contains_3047(locked_requests[pid->val], req0) && req0->id == req->id);
  modifies locked_requests, participant_votes, committed_requests;



implementation Civl_PendingAsyncNoninterferenceChecker_voting_1(req: Request, pid: One_15)
{
  var Civl_global_old_locked_requests: [int]Set_3804;
  var Civl_global_old_participant_votes: [int][Request]Vote;
  var Civl_global_old_committed_requests: Set_3804;
  var Civl_linear_Request_available: [Request]bool;
  var Civl_linear_int_available: [int]bool;

  init:
    Civl_global_old_locked_requests, Civl_global_old_participant_votes, Civl_global_old_committed_requests := locked_requests, participant_votes, committed_requests;
    Civl_linear_Request_available, Civl_linear_int_available := MapConst_5_3804(false), MapOr_15(One_Collector_15(pid), MapConst_5_1195(false));
    call voting(req, pid);
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Request_available, Civl_linear_int_available, Civl_global_old_locked_requests, Civl_global_old_participant_votes, Civl_global_old_committed_requests);
    return;
}



procedure Civl_PendingAsyncNoninterferenceChecker_MAIN_F_1(req: Request) returns (Civl_PAs_voting: [voting]int);
  modifies locked_requests, participant_votes, committed_requests;



implementation Civl_PendingAsyncNoninterferenceChecker_MAIN_F_1(req: Request) returns (Civl_PAs_voting: [voting]int)
{
  var Civl_global_old_locked_requests: [int]Set_3804;
  var Civl_global_old_participant_votes: [int][Request]Vote;
  var Civl_global_old_committed_requests: Set_3804;
  var Civl_linear_Request_available: [Request]bool;
  var Civl_linear_int_available: [int]bool;

  init:
    Civl_global_old_locked_requests, Civl_global_old_participant_votes, Civl_global_old_committed_requests := locked_requests, participant_votes, committed_requests;
    Civl_linear_Request_available, Civl_linear_int_available := MapConst_5_3804(false), MapConst_5_1195(false);
    call Civl_PAs_voting := MAIN_F(req);
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Request_available, Civl_linear_int_available, Civl_global_old_locked_requests, Civl_global_old_participant_votes, Civl_global_old_committed_requests);
    return;
}



procedure {:inline 1} Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Request_in: [Request]bool, 
    Civl_linear_int_in: [int]bool, 
    Civl_global_old_locked_requests: [int]Set_3804, 
    Civl_global_old_participant_votes: [int][Request]Vote, 
    Civl_global_old_committed_requests: Set_3804);



implementation Civl_Wrapper_NoninterferenceChecker_1(Civl_Civl_linear_Request_in: [Request]bool, 
    Civl_Civl_linear_int_in: [int]bool, 
    Civl_Civl_global_old_locked_requests: [int]Set_3804, 
    Civl_Civl_global_old_participant_votes: [int][Request]Vote, 
    Civl_Civl_global_old_committed_requests: Set_3804)
{

  enter:
    goto L_0;

  L_0:
    call Civl_NoninterferenceChecker_yield_YieldTrue(Civl_Civl_linear_Request_in, Civl_Civl_linear_int_in, Civl_Civl_global_old_locked_requests, Civl_Civl_global_old_participant_votes, Civl_Civl_global_old_committed_requests);
    return;
}



implementation Civl_LinearityChecker_MAIN_F(req: Request) returns (Civl_PAs_voting: [voting]int)
{
  var Civl_pa1_voting: voting;
  var Civl_pa2_voting: voting;

  init:
    call Civl_PAs_voting := MAIN_F(req);
    goto Request_out_of_thin_air_voting, Request_duplication_voting, Request_duplication_voting_voting, int_out_of_thin_air_voting, int_duplication_voting, int_duplication_voting_voting;

  Request_out_of_thin_air_voting:
    assume Civl_pa1_voting is voting && Civl_PAs_voting[Civl_pa1_voting] >= 1;
    assert MapImp_3804(MapConst_5_3804(false), old(MapConst_5_3804(false)))
       == MapConst_5_3804(true);
    return;

  Request_duplication_voting:
    assume Civl_pa1_voting is voting && Civl_PAs_voting[Civl_pa1_voting] >= 1;
    assert MapAnd_3804(MapConst_5_3804(false), MapConst_5_3804(false))
       == MapConst_5_3804(false);
    return;

  Request_duplication_voting_voting:
    assume Civl_pa1_voting != Civl_pa2_voting
       && 
      Civl_pa1_voting is voting
       && Civl_pa2_voting is voting
       && 
      Civl_PAs_voting[Civl_pa1_voting] >= 1
       && Civl_PAs_voting[Civl_pa2_voting] >= 1;
    assert MapAnd_3804(MapConst_5_3804(false), MapConst_5_3804(false))
       == MapConst_5_3804(false);
    return;

  int_out_of_thin_air_voting:
    assume Civl_pa1_voting is voting && Civl_PAs_voting[Civl_pa1_voting] >= 1;
    assert MapImp_15(MapOr_15(One_Collector_15(Civl_pa1_voting->pid), MapConst_5_1195(false)), 
        old(MapConst_5_1195(false)))
       == MapConst_5_1195(true);
    return;

  int_duplication_voting:
    assume Civl_pa1_voting is voting && Civl_PAs_voting[Civl_pa1_voting] >= 1;
    assert MapAnd_1215(MapConst_5_1195(false), 
        MapOr_15(One_Collector_15(Civl_pa1_voting->pid), MapConst_5_1195(false)))
       == MapConst_5_1195(false);
    return;

  int_duplication_voting_voting:
    assume Civl_pa1_voting != Civl_pa2_voting
       && 
      Civl_pa1_voting is voting
       && Civl_pa2_voting is voting
       && 
      Civl_PAs_voting[Civl_pa1_voting] >= 1
       && Civl_PAs_voting[Civl_pa2_voting] >= 1;
    assert MapAnd_1215(MapOr_15(One_Collector_15(Civl_pa1_voting->pid), MapConst_5_1195(false)), 
        MapOr_15(One_Collector_15(Civl_pa2_voting->pid), MapConst_5_1195(false)))
       == MapConst_5_1195(false);
    return;
}



procedure Civl_LinearityChecker_MAIN_F(req: Request) returns (Civl_PAs_voting: [voting]int);
  requires true;
  requires true;



procedure Civl_PartitionChecker_MAIN_F(req: Request) returns (Civl_PAs_voting: [voting]int);
  requires true;
  requires true;



implementation Civl_PartitionChecker_MAIN_F(req: Request) returns (Civl_PAs_voting: [voting]int)
{
  var Civl_local_Civl_PAs_voting: voting;

  Civl_PartitionChecker_MAIN_F:
    call Civl_PAs_voting := MAIN_F(req);
    assert Civl_PAs_voting != MapConst_3_6458(0) ==> true;
    goto label_Civl_PAs_voting;

  label_Civl_PAs_voting:
    assume Civl_PAs_voting[Civl_local_Civl_PAs_voting] >= 1;
    assert !(exists req0: Request :: 
      Set_Contains_3047(locked_requests[Civl_local_Civl_PAs_voting->pid->val], req0)
         && req0->id == Civl_local_Civl_PAs_voting->req->id);
    return;
}



procedure Civl_PartitionChecker_voting(req: Request, pid: One_15);
  requires !(exists req0: Request :: 
    Set_Contains_3047(locked_requests[pid->val], req0) && req0->id == req->id);
  requires true;
  requires true;
  modifies locked_requests, participant_votes;



implementation Civl_PartitionChecker_voting(req: Request, pid: One_15)
{

  Civl_PartitionChecker_voting:
    call voting(req, pid);
    assert false ==> true;
    return;
}



procedure Civl_ISR_base_MAIN_F(req: Request) returns (Civl_PAs_voting: [voting]int);
  requires true;
  requires true;
  modifies participant_votes, locked_requests;



implementation Civl_ISR_base_MAIN_F(req: Request) returns (Civl_PAs_voting: [voting]int)
{

  ISR_base_MAIN_F:
    call Civl_PAs_voting := MAIN_F(req);
    assert (exists {:pool "A"} Civl_j#0: int :: 
        0 <= Civl_j#0
           && Civl_j#0 <= n
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0
               ==> participant_votes[i][req] == YES() || participant_votes[i][req] == YES())
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0
               ==> (participant_votes[i][req] == YES()
                 <==> Set_Contains_3047(locked_requests[i], req)))
           && Civl_j#0 < n
           && Civl_PAs_voting
             == MapAdd_6447(MapConst_3_6458(0), 
              MapIte_6465_3((lambda {:pool "C"} pa: voting :: 
                  Civl_j#0 + 1 <= pa->pid->val && pa->pid->val <= n && pa->req == req), 
                MapConst_3_6458(1), 
                MapConst_3_6458(0)))
           && participant_votes == old(participant_votes)
           && locked_requests == old(locked_requests))
       || (exists {:pool "A"} Civl_j#0: int :: 
        0 <= Civl_j#0
           && Civl_j#0 <= n
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0
               ==> participant_votes[i][req] == YES() || participant_votes[i][req] == YES())
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0
               ==> (participant_votes[i][req] == YES()
                 <==> Set_Contains_3047(locked_requests[i], req)))
           && n <= Civl_j#0
           && Civl_PAs_voting == MapConst_3_6458(0)
           && participant_votes == old(participant_votes)
           && locked_requests == old(locked_requests));
    return;
}



procedure Civl_ISR_conclusion_MAIN_F(req: Request) returns (Civl_PAs_voting: [voting]int);
  requires true;
  requires true;
  modifies participant_votes, locked_requests;



implementation Civl_ISR_conclusion_MAIN_F(req: Request) returns (Civl_PAs_voting: [voting]int)
{

  ISR_conclusion_MAIN_F:
    call Civl_PAs_voting := Inv(req);
    assume Civl_PAs_voting == MapConst_3_6458(0);
    assert (forall p: int :: 
        1 <= p && p <= n
           ==> participant_votes[p][req] == YES() || participant_votes[p][req] == NO())
       && (forall p: int :: 
        participant_votes[p][req] == YES()
           <==> Set_Contains_3047(locked_requests[p], req))
       && locked_requests == old(locked_requests)
       && participant_votes == old(participant_votes);
    return;
}



procedure Civl_ISR_step_Inv_voting(req: Request) returns (Civl_PAs_voting: [voting]int, Civl_choice: Choice_Inv);
  requires true;
  requires true;
  modifies participant_votes, locked_requests;



implementation Civl_ISR_step_Inv_voting(req: Request) returns (Civl_PAs_voting: [voting]int, Civl_choice: Choice_Inv)
{

  ISR_step_Inv_voting:
    call Civl_PAs_voting, Civl_choice := Inv_With_Choice(req);
    assume Civl_choice is Choice_Inv_voting;
    assume Civl_PAs_voting[Civl_choice->voting] > 0;
    Civl_PAs_voting[Civl_choice->voting] := Civl_PAs_voting[Civl_choice->voting] - 1;
    assert !(exists req0: Request :: 
      Set_Contains_3047(locked_requests[Civl_choice->voting->pid->val], req0)
         && req0->id == Civl_choice->voting->req->id);
    call voting(Civl_choice->voting->req, Civl_choice->voting->pid);
    assert (exists {:pool "A"} Civl_j#0: int :: 
        0 <= Civl_j#0
           && Civl_j#0 <= n
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0
               ==> participant_votes[i][req] == YES() || participant_votes[i][req] == YES())
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0
               ==> (participant_votes[i][req] == YES()
                 <==> Set_Contains_3047(locked_requests[i], req)))
           && Civl_j#0 < n
           && Civl_PAs_voting
             == MapAdd_6447(MapConst_3_6458(0), 
              MapIte_6465_3((lambda {:pool "C"} pa: voting :: 
                  Civl_j#0 + 1 <= pa->pid->val && pa->pid->val <= n && pa->req == req), 
                MapConst_3_6458(1), 
                MapConst_3_6458(0)))
           && participant_votes == old(participant_votes)
           && locked_requests == old(locked_requests))
       || (exists {:pool "A"} Civl_j#0: int :: 
        0 <= Civl_j#0
           && Civl_j#0 <= n
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0
               ==> participant_votes[i][req] == YES() || participant_votes[i][req] == YES())
           && (forall i: int :: 
            1 <= i && i <= Civl_j#0
               ==> (participant_votes[i][req] == YES()
                 <==> Set_Contains_3047(locked_requests[i], req)))
           && n <= Civl_j#0
           && Civl_PAs_voting == MapConst_3_6458(0)
           && participant_votes == old(participant_votes)
           && locked_requests == old(locked_requests));
    return;
}



procedure Civl_ISR_SideCondition_MAIN_F(req: Request) returns (Civl_PAs_voting: [voting]int);
  requires true;
  requires true;



implementation Civl_ISR_SideCondition_MAIN_F(req: Request) returns (Civl_PAs_voting: [voting]int)
{

  init:
    assume true;
    call Civl_PAs_voting := MAIN_F(req);
    goto Request_only_put_perm_MAIN_F, int_only_put_perm_MAIN_F;

  Request_only_put_perm_MAIN_F:
    assume true;
    assert MapImp_3804(old(MapConst_5_3804(false)), MapConst_5_3804(false))
       == MapConst_5_3804(true);
    return;

  int_only_put_perm_MAIN_F:
    assume true;
    assert MapImp_15(old(MapConst_5_1195(false)), MapConst_5_1195(false))
       == MapConst_5_1195(true);
    return;
}



procedure Civl_ISR_AllPendingAsyncsInElim_voting(req: Request, pid: One_15);
  modifies participant_votes, locked_requests;



implementation Civl_ISR_AllPendingAsyncsInElim_voting(req: Request, pid: One_15)
{

  ISR_AllPendingAsyncsInElim_voting:
    assume !false;
    call voting(req, pid);
    assert true;
    return;
}



procedure Civl_ISR_AllPendingAsyncsNotInElim_voting(req: Request, pid: One_15);
  modifies participant_votes, locked_requests;



implementation Civl_ISR_AllPendingAsyncsNotInElim_voting(req: Request, pid: One_15)
{

  ISR_AllPendingAsyncsNotInElim_voting:
    assume false;
    call voting(req, pid);
    assert true;
    return;
}



procedure Civl_ISR_SideCondition_voting(req: Request, pid: One_15);
  requires !(exists req0: Request :: 
    Set_Contains_3047(locked_requests[pid->val], req0) && req0->id == req->id);
  requires true;
  requires true;
  modifies locked_requests, participant_votes;



implementation Civl_ISR_SideCondition_voting(req: Request, pid: One_15)
{

  init:
    assume !false;
    call voting(req, pid);
    goto Request_only_put_perm_voting, int_only_put_perm_voting;

  Request_only_put_perm_voting:
    assume true;
    assert MapImp_3804(old(MapConst_5_3804(false)), MapConst_5_3804(false))
       == MapConst_5_3804(true);
    return;

  int_only_put_perm_voting:
    assume true;
    assert MapImp_15(old(MapConst_5_1195(false)), MapConst_5_1195(false))
       == MapConst_5_1195(true);
    return;
}



procedure Civl_ISR_InconsistencyChecker_MAIN_F_voting_voting();
  modifies participant_votes, locked_requests;



implementation Civl_ISR_InconsistencyChecker_MAIN_F_voting_voting()
{
  var Civl_E1_voting: voting;
  var Civl_E2_voting: voting;
  var Civl_tempg_locked_requests: [int]Set_3804;
  var Civl_tempg_participant_votes: [int][Request]Vote;
  var Civl_tempg_committed_requests: Set_3804;
  var Civl_templ_req: Request;

  ISR_InconsistencyChecker_MAIN_F_voting_voting:
    assume true;
    assume MapAnd_3804(MapConst_5_3804(false), MapConst_5_3804(false))
         == MapConst_5_3804(false)
       && MapAnd_3804(MapConst_5_3804(false), MapConst_5_3804(false))
         == MapConst_5_3804(false)
       && MapAnd_3804(MapConst_5_3804(false), MapConst_5_3804(false))
         == MapConst_5_3804(false)
       && 
      MapAnd_1215(MapConst_5_1195(false), 
          MapOr_15(One_Collector_15(Civl_E1_voting->pid), MapConst_5_1195(false)))
         == MapConst_5_1195(false)
       && MapAnd_1215(MapConst_5_1195(false), 
          MapOr_15(One_Collector_15(Civl_E2_voting->pid), MapConst_5_1195(false)))
         == MapConst_5_1195(false)
       && MapAnd_1215(MapOr_15(One_Collector_15(Civl_E1_voting->pid), MapConst_5_1195(false)), 
          MapOr_15(One_Collector_15(Civl_E2_voting->pid), MapConst_5_1195(false)))
         == MapConst_5_1195(false);
    assume MapImp_3804(MapConst_5_3804(false), MapConst_5_3804(false))
         == MapConst_5_3804(true)
       && MapImp_3804(MapConst_5_3804(false), MapConst_5_3804(false))
         == MapConst_5_3804(true)
       && 
      MapImp_15(MapOr_15(One_Collector_15(Civl_E1_voting->pid), MapConst_5_1195(false)), 
          MapConst_5_1195(false))
         == MapConst_5_1195(true)
       && MapImp_15(MapOr_15(One_Collector_15(Civl_E2_voting->pid), MapConst_5_1195(false)), 
          MapConst_5_1195(false))
         == MapConst_5_1195(true);
    assert !(!(exists req0: Request :: 
        Set_Contains_3047(locked_requests[Civl_E1_voting->pid->val], req0)
           && req0->id == Civl_E1_voting->req->id)
       && 
      false
       && !(exists req0: Request :: 
        Set_Contains_3047(locked_requests[Civl_E2_voting->pid->val], req0)
           && req0->id == Civl_E2_voting->req->id));
    return;
}


