// Boogie program verifier version 3.2.3.0, Copyright (c) 2003-2014, Microsoft.
// Command Line Options: Easy-PC2-new.bpl /civlDesugaredFile:easy-pc2-sugar.bpl

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

var locked_requests: [int]Set_4061;

var participant_votes: [int][Request]Vote;

var committed_requests: Set_4061;

function {:inline} Init(req: Request, participant_votes: [int][Request]Vote) : bool
{
  (forall p: int :: participant_votes[p][req] == NULL())
}

function {:inline} NoOverlap(req_set: Set_4061, d: int) : bool
{
  !(exists req: Request :: Set_Contains_3248(req_set, req) && req->duration == d)
}

function {:inline} Init2(pids: [int]bool) : bool
{
  pids == MapConst_5_15(true)
}

datatype voting {
  voting(req: Request, pid: One_15)
}

const Identity: [int]int;

function {:inline} AtLeast(x: int) : [int]bool
{
  MapLe_1402(MapConst_1419_1402(x), Identity)
}

function {:inline} Range(from: int, n: int) : [int]bool
{
  MapDiff_1422(AtLeast(from), AtLeast(from + n))
}

type {:builtin "Seq"} Seq _;

pure procedure Assume(b: bool);
  ensures b;



datatype Set_4061 {
  Set_4061(val: [Request]bool)
}

function {:inline} Set_Contains_3248(a: Set_4061, t: Request) : bool
{
  a->val[t]
}

datatype One_15 {
  One_15(val: int)
}

function {:builtin "MapConst"} MapConst_5_15(bool) : [int]bool;

datatype Set_15 {
  Set_15(val: [int]bool)
}

pure procedure One_Get_15(path: Set_15, k: int) returns (l: One_15);



function {:inline} Set_Add_3231(a: Set_4061, t: Request) : Set_4061
{
  Set_4061(a->val[t := true])
}

function {:builtin "MapConst"} MapConst_1419_1402(int) : [int]int;

function {:builtin "MapLe"} MapLe_1402([int]int, [int]int) : [int]bool;

function {:inline} MapDiff_1422(a: [int]bool, b: [int]bool) : [int]bool
{
  MapAnd_1422(a, MapNot_1422(b))
}

function {:builtin "MapNot"} MapNot_1422([int]bool) : [int]bool;

function {:builtin "MapAnd"} MapAnd_1422([int]bool, [int]bool) : [int]bool;

datatype Vec_5 {
  Vec_5(contents: [int]bool, len: int)
}

function Default_5() : bool;

function {:builtin "MapIte"} MapIte_1443_5([int]bool, [int]bool, [int]bool) : [int]bool;

datatype Vec_1419 {
  Vec_1419(contents: [int]int, len: int)
}

function Default_1419() : int;

function {:builtin "MapIte"} MapIte_1443_1419([int]bool, [int]int, [int]int) : [int]int;

function Choice_15(a: [int]bool) : int;

axiom n > 0;

axiom (forall x: int :: Identity[x] == x);

axiom (forall x: Vec_1419 :: 
  { x->len } { x->contents } 
  MapIte_1443_1419(Range(0, x->len), MapConst_1419_1402(Default_1419()), x->contents)
     == MapConst_1419_1402(Default_1419()));

axiom (forall x: Vec_5 :: 
  { x->len } { x->contents } 
  MapIte_1443_5(Range(0, x->len), MapConst_5_15(Default_5()), x->contents)
     == MapConst_5_15(Default_5()));

axiom (forall x: Vec_1419 :: { x->len } x->len >= 0);

axiom (forall x: Vec_5 :: { x->len } x->len >= 0);

axiom (forall a: [int]bool :: 
  { Choice_15(a) } 
  a == MapConst_5_15(false) || a[Choice_15(a)]);

function {:builtin "MapConst"} MapConst_5_4061(bool) : [Request]bool;

function {:builtin "MapConst"} MapConst_3_4061(int) : [Request]int;

function {:builtin "MapAnd"} MapAnd_4061([Request]bool, [Request]bool) : [Request]bool;

function {:builtin "MapOr"} MapOr_4061([Request]bool, [Request]bool) : [Request]bool;

function {:builtin "MapImp"} MapImp_4061([Request]bool, [Request]bool) : [Request]bool;

function {:builtin "MapEq"} MapEq_4061_3([Request]int, [Request]int) : [Request]bool;

function {:builtin "MapAdd"} MapAdd_4061([Request]int, [Request]int) : [Request]int;

function {:builtin "MapIte"} MapIte_4061_3([Request]bool, [Request]int, [Request]int) : [Request]int;

function {:builtin "MapLe"} MapLe_4061([Request]int, [Request]int) : [Request]bool;

function {:inline} Set_Collector_4061(a: Set_4061) : [Request]bool
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
  MapConst_5_15(false)[t := true]
}

function {:inline} Set_Collector_15(a: Set_15) : [int]bool
{
  a->val
}

function {:builtin "MapAdd"} MapAdd_7287([voting]int, [voting]int) : [voting]int;

function {:builtin "MapConst"} MapConst_3_7298(int) : [voting]int;

function {:builtin "MapIte"} MapIte_7305_3([voting]bool, [voting]int, [voting]int) : [voting]int;

function {:inline} Set_Contains_15(a: Set_15, t: int) : bool
{
  a->val[t]
}

function {:inline} Set_Remove_15(a: Set_15, t: int) : Set_15
{
  Set_15(a->val[t := false])
}

procedure ADD_TO_COMMITTED_REQUESTS_GateSufficiencyChecker(req: Request);
  requires !(exists req0: Request :: 
    Set_Contains_3248(committed_requests, req0) && req0->id == req->id);
  requires !(exists req1: Request :: 
    req1->id != req->id
       && req1->duration == req->duration
       && Set_Contains_3248(committed_requests, req1));
  modifies committed_requests;



implementation ADD_TO_COMMITTED_REQUESTS_GateSufficiencyChecker(req: Request)
{
  /*** structured program:
    committed_requests := Set_Add_3231(committed_requests, req);
  **** end structured program */

  anon0:
    committed_requests := Set_Add_3231(committed_requests, req);
    return;
}



implementation voting(req: Request, pid: One_15)
{
  /*** structured program:
    assert !(exists req0: Request :: 
      Set_Contains_3248(locked_requests[pid->val], req0) && req0->id == req->id);
    assert participant_votes[pid->val][req] == NULL();
    if (*)
    {
        participant_votes[pid->val][req] := NO();
        return;
    }
    else
    {
        if (NoOverlap(locked_requests[pid->val], req->duration))
        {
            locked_requests[pid->val] := Set_Add_3231(locked_requests[pid->val], req);
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
    locked_requests[pid->val] := Set_Add_3231(locked_requests[pid->val], req);
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
  (exists Civl_old_locked_requests: [int]Set_4061, 
      Civl_old_participant_votes: [int][Request]Vote, 
      Civl_old_committed_requests: Set_4061, 
      Civl_locked_requests: [int]Set_4061, 
      Civl_participant_votes: [int][Request]Vote, 
      Civl_committed_requests: Set_4061 :: 
    Civl_old_participant_votes[pid->val][req] == NULL()
       && !(exists req0: Request :: 
        Set_Contains_3248(Civl_old_locked_requests[pid->val], req0)
           && req0->id == req->id)
       && (
        (Civl_participant_votes
             == Civl_old_participant_votes[pid->val := Civl_old_participant_votes[pid->val][req := NO()]]
           && Civl_locked_requests == Civl_old_locked_requests)
         || (
          NoOverlap(Civl_old_locked_requests[pid->val], req->duration)
           && Civl_locked_requests
             == Civl_old_locked_requests[pid->val := Set_Add_3231(Civl_old_locked_requests[pid->val], req)]
           && Civl_participant_votes
             == Civl_old_participant_votes[pid->val := Civl_old_participant_votes[pid->val][req := YES()]])
         || (
          !NoOverlap(Civl_locked_requests[pid->val], req->duration)
           && Civl_participant_votes
             == Civl_old_participant_votes[pid->val := Civl_old_participant_votes[pid->val][req := NO()]]
           && Civl_locked_requests == Civl_old_locked_requests)))
}

implementation ADD_TO_COMMITTED_REQUESTS(req: Request)
{
  /*** structured program:
    committed_requests := Set_Add_3231(committed_requests, req);
  **** end structured program */

  anon0:
    committed_requests := Set_Add_3231(committed_requests, req);
    return;
}



procedure {:inline 1} ADD_TO_COMMITTED_REQUESTS(req: Request);
  modifies committed_requests;



function {:inline} Civl_InputOutputRelation_ADD_TO_COMMITTED_REQUESTS(req: Request) : bool
{
  (exists Civl_old_locked_requests: [int]Set_4061, 
      Civl_old_participant_votes: [int][Request]Vote, 
      Civl_old_committed_requests: Set_4061, 
      Civl_locked_requests: [int]Set_4061, 
      Civl_participant_votes: [int][Request]Vote, 
      Civl_committed_requests: Set_4061 :: 
    !(exists req0: Request :: 
        Set_Contains_3248(Civl_old_committed_requests, req0) && req0->id == req->id)
       && !(exists req1: Request :: 
        req1->id != req->id
           && req1->duration == req->duration
           && Set_Contains_3248(Civl_old_committed_requests, req1))
       && Civl_committed_requests == Set_Add_3231(Civl_old_committed_requests, req))
}

implementation RECEIVE_VOTE(pid: int, req: Request) returns (v: Vote)
{
  /*** structured program:
    assume participant_votes[pid][req] != NULL();
    v := participant_votes[pid][req];
  **** end structured program */

  anon0:
    assume participant_votes[pid][req] != NULL();
    v := participant_votes[pid][req];
    return;
}



procedure {:inline 1} RECEIVE_VOTE(pid: int, req: Request) returns (v: Vote);



function {:inline} Civl_InputOutputRelation_RECEIVE_VOTE(pid: int, req: Request, v: Vote) : bool
{
  (exists Civl_old_locked_requests: [int]Set_4061, 
      Civl_old_participant_votes: [int][Request]Vote, 
      Civl_old_committed_requests: Set_4061, 
      Civl_locked_requests: [int]Set_4061, 
      Civl_participant_votes: [int][Request]Vote, 
      Civl_committed_requests: Set_4061 :: 
    Civl_participant_votes[pid][req] != NULL()
       && v == Civl_participant_votes[pid][req])
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
  (exists Civl_old_locked_requests: [int]Set_4061, 
      Civl_old_participant_votes: [int][Request]Vote, 
      Civl_old_committed_requests: Set_4061, 
      Civl_locked_requests: [int]Set_4061, 
      Civl_participant_votes: [int][Request]Vote, 
      Civl_committed_requests: Set_4061 :: 
    (forall pid: int :: 
      1 <= pid && pid <= n ==> Civl_participant_votes[pid][req] != NULL()))
}

implementation Civl_Skip()
{

  init:
    return;
}



pure procedure {:inline 1} Civl_Skip();



function {:inline} Civl_InputOutputRelation_Civl_Skip() : bool
{
  (exists Civl_old_locked_requests: [int]Set_4061, 
      Civl_old_participant_votes: [int][Request]Vote, 
      Civl_old_committed_requests: Set_4061, 
      Civl_locked_requests: [int]Set_4061, 
      Civl_participant_votes: [int][Request]Vote, 
      Civl_committed_requests: Set_4061 :: 
    true)
}

implementation Civl_CommutativityChecker_RECEIVE_VOTE_voting(first_pid: int, first_req: Request, second_req: Request, second_pid: One_15)
   returns (first_v: Vote)
{

  init:
    call first_v := RECEIVE_VOTE(first_pid, first_req);
    call voting(second_req, second_pid);
    assert true
       ==> (
          participant_votes[first_pid][first_req] != NULL()
           && participant_votes
             == old(participant_votes)[second_pid->val := old(participant_votes)[second_pid->val][second_req := NO()]]
           && first_v == participant_votes[first_pid][first_req]
           && locked_requests == old(locked_requests))
         || (
          NoOverlap(old(locked_requests)[second_pid->val], second_req->duration)
           && participant_votes[first_pid][first_req] != NULL()
           && locked_requests
             == old(locked_requests)[second_pid->val := Set_Add_3231(old(locked_requests)[second_pid->val], second_req)]
           && participant_votes
             == old(participant_votes)[second_pid->val := old(participant_votes)[second_pid->val][second_req := YES()]]
           && first_v == participant_votes[first_pid][first_req])
         || (
          !NoOverlap(locked_requests[second_pid->val], second_req->duration)
           && participant_votes[first_pid][first_req] != NULL()
           && participant_votes
             == old(participant_votes)[second_pid->val := old(participant_votes)[second_pid->val][second_req := NO()]]
           && first_v == participant_votes[first_pid][first_req]
           && locked_requests == old(locked_requests));
    return;
}



procedure Civl_CommutativityChecker_RECEIVE_VOTE_voting(first_pid: int, first_req: Request, second_req: Request, second_pid: One_15)
   returns (first_v: Vote);
  requires true;
  requires participant_votes[second_pid->val][second_req] == NULL();
  requires !(exists second_req0: Request :: 
    Set_Contains_3248(locked_requests[second_pid->val], second_req0)
       && second_req0->id == second_req->id);
  modifies locked_requests, participant_votes, committed_requests;



procedure Civl_coordinator_1(cid: int, req: Request, pids: Set_15);
  requires Init(req, participant_votes);
  requires Init2(pids->val);
  requires (forall pid: int, req: Request :: 
    Set_Contains_3248(locked_requests[pid], req)
       <==> participant_votes[pid][req] == YES());
  requires !(exists pid: int, req1: Request, req2: Request :: 
    req1->id != req2->id
       && req1->duration == req2->duration
       && Set_Contains_3248(locked_requests[pid], req1)
       && Set_Contains_3248(locked_requests[pid], req2));
  requires !(exists req1: Request, req2: Request :: 
    req1->id != req2->id
       && req1->duration == req2->duration
       && Set_Contains_3248(committed_requests, req1)
       && Set_Contains_3248(committed_requests, req2));
  requires !(exists req: Request, pid: int :: 
    Set_Contains_3248(committed_requests, req)
       && !Set_Contains_3248(locked_requests[pid], req));
  modifies locked_requests, participant_votes, committed_requests;



procedure Civl_voting0_1(req: Request, pid: One_15);
  requires (forall pid: int, req: Request :: 
    Set_Contains_3248(locked_requests[pid], req)
       <==> participant_votes[pid][req] == YES());
  requires !(exists pid: int, req1: Request, req2: Request :: 
    req1->id != req2->id
       && req1->duration == req2->duration
       && Set_Contains_3248(locked_requests[pid], req1)
       && Set_Contains_3248(locked_requests[pid], req2));
  requires !(exists req1: Request, req2: Request :: 
    req1->id != req2->id
       && req1->duration == req2->duration
       && Set_Contains_3248(committed_requests, req1)
       && Set_Contains_3248(committed_requests, req2));
  requires !(exists req: Request, pid: int :: 
    Set_Contains_3248(committed_requests, req)
       && !Set_Contains_3248(locked_requests[pid], req));
  requires !(exists req0: Request :: 
    Set_Contains_3248(locked_requests[pid->val], req0) && req0->id == req->id);
  requires participant_votes[pid->val][req] == NULL();
  modifies locked_requests, participant_votes, committed_requests;



implementation Civl_coordinator_1(cid: int, req: Request, pids: Set_15)
{
  var i: int;
  var j: int;
  var d: Decision;
  var v: Vote;
  var pid: One_15;
  var pids': Set_15;
  var Civl_global_old_locked_requests: [int]Set_4061;
  var Civl_global_old_participant_votes: [int][Request]Vote;
  var Civl_global_old_committed_requests: Set_4061;
  var Civl_pc: bool;
  var Civl_ok: bool;
  var Civl_eval: bool;
  var Civl_linear_Request_available: [Request]bool;
  var Civl_linear_int_available: [int]bool;

  /*** structured program:
    d := COMMIT();
    j := 1;
    pids' := pids;
    while (j <= n)
    {
        assert old(participant_votes)[j][req] == NULL();
        call pid := One_Get(pids', j);
        async call voting0(req, pid);
        j := j + 1;
    }

    call YieldBig();
    i := 1;
    while (i <= n)
    {
        call v := receive_vote(i, req);
        if (v == NO())
        {
            d := ABORT();
        }

        i := i + 1;
    }

    call YieldBig();
    if (d == COMMIT())
    {
        assume false;
        assert !(exists req1: Request :: 
          req1->id != req->id
             && req1->duration == req->duration
             && Set_Contains_3248(committed_requests, req1));
        call add_to_committed_requests(req);
    }
  **** end structured program */

  Civl_init:
    havoc locked_requests, participant_votes, committed_requests;
    assume Init(old(req), participant_votes);
    assume Init2(old(pids)->val);
    assume (forall pid: int, req: Request :: 
      Set_Contains_3248(locked_requests[pid], req)
         <==> participant_votes[pid][req] == YES());
    assume !(exists pid: int, req1: Request, req2: Request :: 
      req1->id != req2->id
         && req1->duration == req2->duration
         && Set_Contains_3248(locked_requests[pid], req1)
         && Set_Contains_3248(locked_requests[pid], req2));
    assume !(exists req1: Request, req2: Request :: 
      req1->id != req2->id
         && req1->duration == req2->duration
         && Set_Contains_3248(committed_requests, req1)
         && Set_Contains_3248(committed_requests, req2));
    assume !(exists req: Request, pid: int :: 
      Set_Contains_3248(committed_requests, req)
         && !Set_Contains_3248(locked_requests[pid], req));
    Civl_global_old_locked_requests, Civl_global_old_participant_votes, Civl_global_old_committed_requests := locked_requests, participant_votes, committed_requests;
    Civl_pc, Civl_ok, Civl_eval := false, false, false;
    assume true;
    Civl_linear_Request_available, Civl_linear_int_available := MapConst_5_4061(false), MapOr_15(Set_Collector_15(pids), MapConst_5_15(false));
    goto anon0;

  anon0:
    d := COMMIT();
    j := 1;
    pids' := pids;
    goto anon8_LoopHead;

  anon8_LoopHead:
    goto anon8_LoopDone, anon8_LoopBody;

  anon8_LoopBody:
    assume {:partition} j <= n;
    assert old(participant_votes)[j][req] == NULL();
    assert Set_Contains_15(pids', j);
    pids' := Set_Remove_15(pids', j);
    pid := One_15(j);
    call Civl_AsyncCall_voting0_1(req, pid);
    j := j + 1;
    goto anon8_LoopHead;

  anon8_LoopDone:
    assume {:partition} n < j;
    goto anon2;

  anon2:
    Civl_eval := true;
    goto anon2_0, Civl_NoninterferenceChecker, Civl_RefinementChecker;

  anon2_0:
    Civl_pc, Civl_ok := true ==> Civl_pc, Civl_eval || Civl_ok;
    call Civl_ParallelCall_YieldBig_1();
    assume Civl_pc || true;
    Civl_global_old_locked_requests, Civl_global_old_participant_votes, Civl_global_old_committed_requests := locked_requests, participant_votes, committed_requests;
    Civl_linear_Request_available, Civl_linear_int_available := MapConst_5_4061(false), MapOr_15(Set_Collector_15(pids'), MapConst_5_15(false));
    i := 1;
    goto anon9_LoopHead;

  anon9_LoopHead:
    goto anon9_LoopDone, anon9_LoopBody;

  anon9_LoopBody:
    assume {:partition} i <= n;
    call v := RECEIVE_VOTE(i, req);
    goto anon10_Then, anon10_Else;

  anon10_Else:
    assume {:partition} v != NO();
    goto anon5;

  anon5:
    i := i + 1;
    goto anon9_LoopHead;

  anon10_Then:
    assume {:partition} v == NO();
    d := ABORT();
    goto anon5;

  anon9_LoopDone:
    assume {:partition} n < i;
    goto anon6;

  anon6:
    Civl_eval := true;
    goto anon6_0, Civl_NoninterferenceChecker, Civl_RefinementChecker;

  anon6_0:
    Civl_pc, Civl_ok := true ==> Civl_pc, Civl_eval || Civl_ok;
    call Civl_ParallelCall_YieldBig_1();
    assume Civl_pc || true;
    Civl_global_old_locked_requests, Civl_global_old_participant_votes, Civl_global_old_committed_requests := locked_requests, participant_votes, committed_requests;
    Civl_linear_Request_available, Civl_linear_int_available := MapConst_5_4061(false), MapOr_15(Set_Collector_15(pids'), MapConst_5_15(false));
    goto anon11_Then, anon11_Else;

  anon11_Else:
    assume {:partition} d != COMMIT();
    goto Civl_ReturnChecker, Civl_UnifiedReturn, Civl_NoninterferenceChecker;

  anon11_Then:
    assume {:partition} d == COMMIT();
    assume false;
    assert !(exists req1: Request :: 
      req1->id != req->id
         && req1->duration == req->duration
         && Set_Contains_3248(committed_requests, req1));
    // <<< injected gate
    assert !(exists req0: Request :: 
      Set_Contains_3248(committed_requests, req0) && req0->id == req->id);
    assert !(exists req1: Request :: 
      req1->id != req->id
         && req1->duration == req->duration
         && Set_Contains_3248(committed_requests, req1));
    // injected gate >>>
    call ADD_TO_COMMITTED_REQUESTS(req);
    goto Civl_ReturnChecker, Civl_UnifiedReturn, Civl_NoninterferenceChecker;

  Civl_NoninterferenceChecker:
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Request_available, Civl_linear_int_available, Civl_global_old_locked_requests, Civl_global_old_participant_votes, Civl_global_old_committed_requests);
    assume false;
    return;

  Civl_RefinementChecker:
    assert true;
    assert Civl_pc ==> true;
    assume false;
    return;

  Civl_UnchangedChecker:
    assert true;
    assert Civl_pc ==> true;
    assume false;
    return;

  Civl_ReturnChecker:
    Civl_eval := true;
    assert true;
    assert Civl_pc ==> true;
    Civl_pc, Civl_ok := true ==> Civl_pc, Civl_eval || Civl_ok;
    assert Civl_ok;
    assume false;
    return;

  Civl_UnifiedReturn:
    return;
}



implementation Civl_voting0_1(req: Request, pid: One_15)
{
  var Civl_global_old_locked_requests: [int]Set_4061;
  var Civl_global_old_participant_votes: [int][Request]Vote;
  var Civl_global_old_committed_requests: Set_4061;
  var Civl_pc: bool;
  var Civl_ok: bool;
  var Civl_eval: bool;
  var Civl_linear_Request_available: [Request]bool;
  var Civl_linear_int_available: [int]bool;

  /*** structured program:
    call voting1(req, pid);
  **** end structured program */

  Civl_init:
    havoc locked_requests, participant_votes, committed_requests;
    assume (forall pid: int, req: Request :: 
      Set_Contains_3248(locked_requests[pid], req)
         <==> participant_votes[pid][req] == YES());
    assume !(exists pid: int, req1: Request, req2: Request :: 
      req1->id != req2->id
         && req1->duration == req2->duration
         && Set_Contains_3248(locked_requests[pid], req1)
         && Set_Contains_3248(locked_requests[pid], req2));
    assume !(exists req1: Request, req2: Request :: 
      req1->id != req2->id
         && req1->duration == req2->duration
         && Set_Contains_3248(committed_requests, req1)
         && Set_Contains_3248(committed_requests, req2));
    assume !(exists req: Request, pid: int :: 
      Set_Contains_3248(committed_requests, req)
         && !Set_Contains_3248(locked_requests[pid], req));
    assume !(exists req0: Request :: 
      Set_Contains_3248(locked_requests[old(pid)->val], req0)
         && req0->id == old(req)->id);
    assume participant_votes[old(pid)->val][old(req)] == NULL();
    Civl_global_old_locked_requests, Civl_global_old_participant_votes, Civl_global_old_committed_requests := locked_requests, participant_votes, committed_requests;
    Civl_pc, Civl_ok, Civl_eval := false, false, false;
    assume true;
    Civl_linear_Request_available, Civl_linear_int_available := MapConst_5_4061(false), MapOr_15(One_Collector_15(pid), MapConst_5_15(false));
    goto anon0;

  anon0:
    // <<< injected gate
    assert participant_votes[pid->val][req] == NULL();
    assert !(exists req0: Request :: 
      Set_Contains_3248(locked_requests[pid->val], req0) && req0->id == req->id);
    // injected gate >>>
    call voting(req, pid);
    goto Civl_ReturnChecker, Civl_UnifiedReturn, Civl_NoninterferenceChecker;

  Civl_NoninterferenceChecker:
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Request_available, Civl_linear_int_available, Civl_global_old_locked_requests, Civl_global_old_participant_votes, Civl_global_old_committed_requests);
    assume false;
    return;

  Civl_RefinementChecker:
    assert true;
    assert Civl_pc ==> true;
    assume false;
    return;

  Civl_UnchangedChecker:
    assert true;
    assert Civl_pc ==> true;
    assume false;
    return;

  Civl_ReturnChecker:
    Civl_eval := true;
    assert true;
    assert Civl_pc ==> true;
    Civl_pc, Civl_ok := true ==> Civl_pc, Civl_eval || Civl_ok;
    assert Civl_ok;
    assume false;
    return;

  Civl_UnifiedReturn:
    return;
}



procedure Civl_AsyncCall_voting0_1(req: Request, pid: One_15);
  requires (forall pid: int, req: Request :: 
    Set_Contains_3248(locked_requests[pid], req)
       <==> participant_votes[pid][req] == YES());
  requires !(exists pid: int, req1: Request, req2: Request :: 
    req1->id != req2->id
       && req1->duration == req2->duration
       && Set_Contains_3248(locked_requests[pid], req1)
       && Set_Contains_3248(locked_requests[pid], req2));
  requires !(exists req1: Request, req2: Request :: 
    req1->id != req2->id
       && req1->duration == req2->duration
       && Set_Contains_3248(committed_requests, req1)
       && Set_Contains_3248(committed_requests, req2));
  requires !(exists req: Request, pid: int :: 
    Set_Contains_3248(committed_requests, req)
       && !Set_Contains_3248(locked_requests[pid], req));
  requires !(exists req0: Request :: 
    Set_Contains_3248(locked_requests[pid->val], req0) && req0->id == req->id);
  requires participant_votes[pid->val][req] == NULL();



procedure {:inline 1} Civl_NoninterferenceChecker_yield_YieldInit(Civl_linear_Request_in: [Request]bool, 
    Civl_linear_int_in: [int]bool, 
    Civl_snapshot_locked_requests: [int]Set_4061, 
    Civl_snapshot_participant_votes: [int][Request]Vote, 
    Civl_snapshot_committed_requests: Set_4061);



implementation Civl_NoninterferenceChecker_yield_YieldInit(Civl_linear_Request_in: [Request]bool, 
    Civl_linear_int_in: [int]bool, 
    Civl_snapshot_locked_requests: [int]Set_4061, 
    Civl_snapshot_participant_votes: [int][Request]Vote, 
    Civl_snapshot_committed_requests: Set_4061)
{
  var req: Request;

  enter:
    goto exit, L;

  exit:
    return;

  L:
    assume Init(req, Civl_snapshot_participant_votes);
    assert Init(req, participant_votes);
    assume false;
    return;
}



procedure {:inline 1} Civl_NoninterferenceChecker_yield_YieldBig(Civl_linear_Request_in: [Request]bool, 
    Civl_linear_int_in: [int]bool, 
    Civl_snapshot_locked_requests: [int]Set_4061, 
    Civl_snapshot_participant_votes: [int][Request]Vote, 
    Civl_snapshot_committed_requests: Set_4061);



implementation Civl_NoninterferenceChecker_yield_YieldBig(Civl_linear_Request_in: [Request]bool, 
    Civl_linear_int_in: [int]bool, 
    Civl_snapshot_locked_requests: [int]Set_4061, 
    Civl_snapshot_participant_votes: [int][Request]Vote, 
    Civl_snapshot_committed_requests: Set_4061)
{

  enter:
    goto exit, L;

  exit:
    return;

  L:
    assume (forall pid: int, req: Request :: 
      Set_Contains_3248(Civl_snapshot_locked_requests[pid], req)
         <==> Civl_snapshot_participant_votes[pid][req] == YES());
    assume !(exists pid: int, req1: Request, req2: Request :: 
      req1->id != req2->id
         && req1->duration == req2->duration
         && Set_Contains_3248(Civl_snapshot_locked_requests[pid], req1)
         && Set_Contains_3248(Civl_snapshot_locked_requests[pid], req2));
    assume !(exists req1: Request, req2: Request :: 
      req1->id != req2->id
         && req1->duration == req2->duration
         && Set_Contains_3248(Civl_snapshot_committed_requests, req1)
         && Set_Contains_3248(Civl_snapshot_committed_requests, req2));
    assume !(exists req: Request, pid: int :: 
      Set_Contains_3248(Civl_snapshot_committed_requests, req)
         && !Set_Contains_3248(Civl_snapshot_locked_requests[pid], req));
    assert (forall pid: int, req: Request :: 
      Set_Contains_3248(locked_requests[pid], req)
         <==> participant_votes[pid][req] == YES());
    assert !(exists pid: int, req1: Request, req2: Request :: 
      req1->id != req2->id
         && req1->duration == req2->duration
         && Set_Contains_3248(locked_requests[pid], req1)
         && Set_Contains_3248(locked_requests[pid], req2));
    assert !(exists req1: Request, req2: Request :: 
      req1->id != req2->id
         && req1->duration == req2->duration
         && Set_Contains_3248(committed_requests, req1)
         && Set_Contains_3248(committed_requests, req2));
    assert !(exists req: Request, pid: int :: 
      Set_Contains_3248(committed_requests, req)
         && !Set_Contains_3248(locked_requests[pid], req));
    assume false;
    return;
}



procedure {:inline 1} Civl_NoninterferenceChecker_yield_YieldTrue(Civl_linear_Request_in: [Request]bool, 
    Civl_linear_int_in: [int]bool, 
    Civl_snapshot_locked_requests: [int]Set_4061, 
    Civl_snapshot_participant_votes: [int][Request]Vote, 
    Civl_snapshot_committed_requests: Set_4061);



implementation Civl_NoninterferenceChecker_yield_YieldTrue(Civl_linear_Request_in: [Request]bool, 
    Civl_linear_int_in: [int]bool, 
    Civl_snapshot_locked_requests: [int]Set_4061, 
    Civl_snapshot_participant_votes: [int][Request]Vote, 
    Civl_snapshot_committed_requests: Set_4061)
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



procedure {:inline 1} Civl_NoninterferenceChecker_yield_YieldVoting(Civl_linear_Request_in: [Request]bool, 
    Civl_linear_int_in: [int]bool, 
    Civl_snapshot_locked_requests: [int]Set_4061, 
    Civl_snapshot_participant_votes: [int][Request]Vote, 
    Civl_snapshot_committed_requests: Set_4061);



implementation Civl_NoninterferenceChecker_yield_YieldVoting(Civl_linear_Request_in: [Request]bool, 
    Civl_linear_int_in: [int]bool, 
    Civl_snapshot_locked_requests: [int]Set_4061, 
    Civl_snapshot_participant_votes: [int][Request]Vote, 
    Civl_snapshot_committed_requests: Set_4061)
{
  var pid: One_15;
  var req: Request;

  enter:
    goto exit, L;

  exit:
    return;

  L:
    assume (exists Civl_partition_int: [int]int :: 
      MapImp_15(One_Collector_15(pid), MapEq_15_3(Civl_partition_int, MapConst_1419_1402(0)))
           == MapConst_5_15(true)
         && MapImp_15(Civl_linear_int_in, MapEq_15_3(Civl_partition_int, MapConst_1419_1402(1)))
           == MapConst_5_15(true));
    assume !(exists req0: Request :: 
      Set_Contains_3248(Civl_snapshot_locked_requests[pid->val], req0)
         && req0->id == req->id);
    assume Civl_snapshot_participant_votes[pid->val][req] == NULL();
    assert !(exists req0: Request :: 
      Set_Contains_3248(locked_requests[pid->val], req0) && req0->id == req->id);
    assert participant_votes[pid->val][req] == NULL();
    assume false;
    return;
}



procedure {:inline 1} Civl_NoninterferenceChecker_yield_YieldInit2(Civl_linear_Request_in: [Request]bool, 
    Civl_linear_int_in: [int]bool, 
    Civl_snapshot_locked_requests: [int]Set_4061, 
    Civl_snapshot_participant_votes: [int][Request]Vote, 
    Civl_snapshot_committed_requests: Set_4061);



implementation Civl_NoninterferenceChecker_yield_YieldInit2(Civl_linear_Request_in: [Request]bool, 
    Civl_linear_int_in: [int]bool, 
    Civl_snapshot_locked_requests: [int]Set_4061, 
    Civl_snapshot_participant_votes: [int][Request]Vote, 
    Civl_snapshot_committed_requests: Set_4061)
{
  var pids: Set_15;

  enter:
    goto exit, L;

  exit:
    return;

  L:
    assume (exists Civl_partition_int: [int]int :: 
      MapImp_15(Set_Collector_15(pids), MapEq_15_3(Civl_partition_int, MapConst_1419_1402(0)))
           == MapConst_5_15(true)
         && MapImp_15(Civl_linear_int_in, MapEq_15_3(Civl_partition_int, MapConst_1419_1402(1)))
           == MapConst_5_15(true));
    assume Init2(pids->val);
    assert Init2(pids->val);
    assume false;
    return;
}



procedure Civl_ParallelCall_YieldBig_1();
  requires (forall pid: int, req: Request :: 
    Set_Contains_3248(locked_requests[pid], req)
       <==> participant_votes[pid][req] == YES());
  requires !(exists pid: int, req1: Request, req2: Request :: 
    req1->id != req2->id
       && req1->duration == req2->duration
       && Set_Contains_3248(locked_requests[pid], req1)
       && Set_Contains_3248(locked_requests[pid], req2));
  requires !(exists req1: Request, req2: Request :: 
    req1->id != req2->id
       && req1->duration == req2->duration
       && Set_Contains_3248(committed_requests, req1)
       && Set_Contains_3248(committed_requests, req2));
  requires !(exists req: Request, pid: int :: 
    Set_Contains_3248(committed_requests, req)
       && !Set_Contains_3248(locked_requests[pid], req));
  modifies locked_requests, participant_votes, committed_requests;
  ensures (forall pid: int, req: Request :: 
    Set_Contains_3248(locked_requests[pid], req)
       <==> participant_votes[pid][req] == YES());
  ensures !(exists pid: int, req1: Request, req2: Request :: 
    req1->id != req2->id
       && req1->duration == req2->duration
       && Set_Contains_3248(locked_requests[pid], req1)
       && Set_Contains_3248(locked_requests[pid], req2));
  ensures !(exists req1: Request, req2: Request :: 
    req1->id != req2->id
       && req1->duration == req2->duration
       && Set_Contains_3248(committed_requests, req1)
       && Set_Contains_3248(committed_requests, req2));
  ensures !(exists req: Request, pid: int :: 
    Set_Contains_3248(committed_requests, req)
       && !Set_Contains_3248(locked_requests[pid], req));



procedure Civl_PendingAsyncNoninterferenceChecker_voting_1(req: Request, pid: One_15);
  requires participant_votes[pid->val][req] == NULL();
  requires !(exists req0: Request :: 
    Set_Contains_3248(locked_requests[pid->val], req0) && req0->id == req->id);
  modifies locked_requests, participant_votes, committed_requests;



implementation Civl_PendingAsyncNoninterferenceChecker_voting_1(req: Request, pid: One_15)
{
  var Civl_global_old_locked_requests: [int]Set_4061;
  var Civl_global_old_participant_votes: [int][Request]Vote;
  var Civl_global_old_committed_requests: Set_4061;
  var Civl_linear_Request_available: [Request]bool;
  var Civl_linear_int_available: [int]bool;

  init:
    Civl_global_old_locked_requests, Civl_global_old_participant_votes, Civl_global_old_committed_requests := locked_requests, participant_votes, committed_requests;
    Civl_linear_Request_available, Civl_linear_int_available := MapConst_5_4061(false), MapOr_15(One_Collector_15(pid), MapConst_5_15(false));
    call voting(req, pid);
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Request_available, Civl_linear_int_available, Civl_global_old_locked_requests, Civl_global_old_participant_votes, Civl_global_old_committed_requests);
    return;
}



procedure {:inline 1} Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Request_in: [Request]bool, 
    Civl_linear_int_in: [int]bool, 
    Civl_global_old_locked_requests: [int]Set_4061, 
    Civl_global_old_participant_votes: [int][Request]Vote, 
    Civl_global_old_committed_requests: Set_4061);



implementation Civl_Wrapper_NoninterferenceChecker_1(Civl_Civl_linear_Request_in: [Request]bool, 
    Civl_Civl_linear_int_in: [int]bool, 
    Civl_Civl_global_old_locked_requests: [int]Set_4061, 
    Civl_Civl_global_old_participant_votes: [int][Request]Vote, 
    Civl_Civl_global_old_committed_requests: Set_4061)
{

  enter:
    goto L_0, L_1, L_2, L_3, L_4;

  L_0:
    call Civl_NoninterferenceChecker_yield_YieldInit(Civl_Civl_linear_Request_in, Civl_Civl_linear_int_in, Civl_Civl_global_old_locked_requests, Civl_Civl_global_old_participant_votes, Civl_Civl_global_old_committed_requests);
    return;

  L_1:
    call Civl_NoninterferenceChecker_yield_YieldBig(Civl_Civl_linear_Request_in, Civl_Civl_linear_int_in, Civl_Civl_global_old_locked_requests, Civl_Civl_global_old_participant_votes, Civl_Civl_global_old_committed_requests);
    return;

  L_2:
    call Civl_NoninterferenceChecker_yield_YieldTrue(Civl_Civl_linear_Request_in, Civl_Civl_linear_int_in, Civl_Civl_global_old_locked_requests, Civl_Civl_global_old_participant_votes, Civl_Civl_global_old_committed_requests);
    return;

  L_3:
    call Civl_NoninterferenceChecker_yield_YieldVoting(Civl_Civl_linear_Request_in, Civl_Civl_linear_int_in, Civl_Civl_global_old_locked_requests, Civl_Civl_global_old_participant_votes, Civl_Civl_global_old_committed_requests);
    return;

  L_4:
    call Civl_NoninterferenceChecker_yield_YieldInit2(Civl_Civl_linear_Request_in, Civl_Civl_linear_int_in, Civl_Civl_global_old_locked_requests, Civl_Civl_global_old_participant_votes, Civl_Civl_global_old_committed_requests);
    return;
}


