// Boogie program verifier version 3.2.3.0, Copyright (c) 2003-2014, Microsoft.
// Command Line Options: Easy-PC2-new.bpl /civlDesugaredFile:epc2s.bpl

type Pid = int;

type Duration = int;

type ReqId;

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

datatype Request {
  Request(id: ReqId, duration: int)
}

type ParticipantPiece = Fraction_4429_14;

const NumParticipants: int;

var locked_requests: [int]Set_4510;

var participant_votes: [int][ReqId]Vote;

var committed_requests: Set_4510;

function {:inline} NoOverlap(req_set: Set_4510, d: int) : bool
{
  !(exists req: Request :: Set_Contains_3555(req_set, req) && req->duration == d)
}

function {:inline} JParticipantIds(j: int) : Set_14
{
  Set_14((lambda {:pool "P1"} x: int :: j <= x && x <= NumParticipants))
}

function {:inline} JParticipantPieces(r: ReqId, j: int) : Set_5915
{
  Set_5915((lambda {:pool "P2"} x: Fraction_4429_14 :: 
      x->val == r
         && x->ids == ParticipantIds()
         && Set_Contains_14(JParticipantIds(j), x->id)))
}

function {:inline} AllParticipantPieces(r: ReqId) : Set_5915
{
  Set_5915((lambda {:pool "P2"} x: Fraction_4429_14 :: 
      x->val == r && x->ids == ParticipantIds() && Set_Contains_14(x->ids, x->id)))
}

function {:inline} ParticipantIds() : Set_14
{
  Set_14((lambda {:pool "P1"} x: int :: 1 <= x && x <= NumParticipants))
}

function {:inline} IsValidParticipantPiece(x: Fraction_4429_14) : bool
{
  x->ids == ParticipantIds() && Set_Contains_14(x->ids, x->id)
}

datatype voting {
  voting(req: Request, piece: One_5506)
}

const Identity: [int]int;

function {:inline} AtLeast(x: int) : [int]bool
{
  MapLe_1711(MapConst_1728_1711(x), Identity)
}

function {:inline} Range(from: int, n: int) : [int]bool
{
  MapDiff_1731(AtLeast(from), AtLeast(from + n))
}

type {:builtin "Seq"} Seq _;

pure procedure Assume(b: bool);
  ensures b;



datatype Fraction_4429_14 {
  Fraction_4429_14(val: ReqId, id: int, ids: Set_14)
}

datatype Set_14 {
  Set_14(val: [int]bool)
}

datatype Set_4510 {
  Set_4510(val: [Request]bool)
}

function {:inline} Set_Contains_3555(a: Set_4510, t: Request) : bool
{
  a->val[t]
}

function {:inline} Set_Contains_14(a: Set_14, t: int) : bool
{
  a->val[t]
}

datatype One_5506 {
  One_5506(val: Fraction_4429_14)
}

datatype Set_5915 {
  Set_5915(val: [Fraction_4429_14]bool)
}

function {:inline} Set_Contains_6188(a: Set_5915, t: Fraction_4429_14) : bool
{
  a->val[t]
}

pure procedure One_Get_6622(path: Set_5915, k: Fraction_4429_14) returns (l: One_5506);



function {:inline} Set_Add_3545(a: Set_4510, t: Request) : Set_4510
{
  Set_4510(a->val[t := true])
}

function {:builtin "MapConst"} MapConst_1728_1711(int) : [int]int;

function {:builtin "MapLe"} MapLe_1711([int]int, [int]int) : [int]bool;

function {:inline} MapDiff_1731(a: [int]bool, b: [int]bool) : [int]bool
{
  MapAnd_1731(a, MapNot_1731(b))
}

function {:builtin "MapNot"} MapNot_1731([int]bool) : [int]bool;

function {:builtin "MapAnd"} MapAnd_1731([int]bool, [int]bool) : [int]bool;

datatype Vec_1728 {
  Vec_1728(contents: [int]int, len: int)
}

function Default_1728() : int;

function {:builtin "MapIte"} MapIte_1752_1728([int]bool, [int]int, [int]int) : [int]int;

function {:builtin "MapConst"} MapConst_5_1711(bool) : [int]bool;

function Choice_1711(a: [int]bool) : int;

datatype Vec_5 {
  Vec_5(contents: [int]bool, len: int)
}

function Default_5() : bool;

function {:builtin "MapIte"} MapIte_1752_5([int]bool, [int]bool, [int]bool) : [int]bool;

axiom NumParticipants > 0;

axiom !(exists req1: Request, req2: Request :: 
  req1->id == req2->id && req1->duration != req2->duration);

axiom false;

axiom (forall x: int :: Identity[x] == x);

axiom (forall x: Vec_5 :: 
  { x->len } { x->contents } 
  MapIte_1752_5(Range(0, x->len), MapConst_5_1711(Default_5()), x->contents)
     == MapConst_5_1711(Default_5()));

axiom (forall x: Vec_1728 :: 
  { x->len } { x->contents } 
  MapIte_1752_1728(Range(0, x->len), MapConst_1728_1711(Default_1728()), x->contents)
     == MapConst_1728_1711(Default_1728()));

axiom (forall x: Vec_5 :: { x->len } x->len >= 0);

axiom (forall x: Vec_1728 :: { x->len } x->len >= 0);

axiom (forall a: [int]bool :: 
  { Choice_1711(a) } 
  a == MapConst_5_1711(false) || a[Choice_1711(a)]);

function {:builtin "MapConst"} MapConst_5_4510(bool) : [Request]bool;

function {:builtin "MapConst"} MapConst_3_4510(int) : [Request]int;

function {:builtin "MapAnd"} MapAnd_4510([Request]bool, [Request]bool) : [Request]bool;

function {:builtin "MapOr"} MapOr_4510([Request]bool, [Request]bool) : [Request]bool;

function {:builtin "MapImp"} MapImp_4510([Request]bool, [Request]bool) : [Request]bool;

function {:builtin "MapEq"} MapEq_4510_3([Request]int, [Request]int) : [Request]bool;

function {:builtin "MapAdd"} MapAdd_4510([Request]int, [Request]int) : [Request]int;

function {:builtin "MapIte"} MapIte_4510_3([Request]bool, [Request]int, [Request]int) : [Request]int;

function {:builtin "MapLe"} MapLe_4510([Request]int, [Request]int) : [Request]bool;

function {:inline} Set_Collector_4510(a: Set_4510) : [Request]bool
{
  a->val
}

function {:builtin "MapConst"} MapConst_5_5506(bool) : [Fraction_4429_14]bool;

function {:builtin "MapConst"} MapConst_3_5506(int) : [Fraction_4429_14]int;

function {:builtin "MapAnd"} MapAnd_5506([Fraction_4429_14]bool, [Fraction_4429_14]bool) : [Fraction_4429_14]bool;

function {:builtin "MapOr"} MapOr_5506([Fraction_4429_14]bool, [Fraction_4429_14]bool) : [Fraction_4429_14]bool;

function {:builtin "MapImp"} MapImp_5506([Fraction_4429_14]bool, [Fraction_4429_14]bool) : [Fraction_4429_14]bool;

function {:builtin "MapEq"} MapEq_5506_3([Fraction_4429_14]int, [Fraction_4429_14]int) : [Fraction_4429_14]bool;

function {:builtin "MapAdd"} MapAdd_5506([Fraction_4429_14]int, [Fraction_4429_14]int) : [Fraction_4429_14]int;

function {:builtin "MapIte"} MapIte_5506_3([Fraction_4429_14]bool, [Fraction_4429_14]int, [Fraction_4429_14]int)
   : [Fraction_4429_14]int;

function {:builtin "MapLe"} MapLe_5506([Fraction_4429_14]int, [Fraction_4429_14]int) : [Fraction_4429_14]bool;

function {:inline} One_Collector_5506(a: One_5506) : [Fraction_4429_14]bool
{
  MapOne_5506(a->val)
}

function {:inline} MapOne_5506(t: Fraction_4429_14) : [Fraction_4429_14]bool
{
  MapConst_5_5506(false)[t := true]
}

function {:builtin "MapOr"} MapOr_14([int]bool, [int]bool) : [int]bool;

function {:builtin "MapImp"} MapImp_14([int]bool, [int]bool) : [int]bool;

function {:builtin "MapEq"} MapEq_14_3([int]int, [int]int) : [int]bool;

function {:builtin "MapAdd"} MapAdd_14([int]int, [int]int) : [int]int;

function {:inline} Set_Collector_14(a: Set_14) : [int]bool
{
  a->val
}

function {:inline} Set_Collector_5915(a: Set_5915) : [Fraction_4429_14]bool
{
  a->val
}

function {:builtin "MapAdd"} MapAdd_9397([voting]int, [voting]int) : [voting]int;

function {:builtin "MapConst"} MapConst_3_9408(int) : [voting]int;

function {:builtin "MapIte"} MapIte_9415_3([voting]bool, [voting]int, [voting]int) : [voting]int;

function {:inline} Set_Remove_6622(a: Set_5915, t: Fraction_4429_14) : Set_5915
{
  Set_5915(a->val[t := false])
}

procedure voting_GateSufficiencyChecker(req: Request, piece: One_5506);
  requires IsValidParticipantPiece(piece->val) && piece->val->val == req->id;
  requires participant_votes[piece->val->id][piece->val->val] == NULL();
  modifies locked_requests, participant_votes;



implementation voting_GateSufficiencyChecker(req: Request, piece: One_5506)
{
  /*** structured program:
    if (NoOverlap(locked_requests[piece->val->id], req->duration))
    {
        locked_requests[piece->val->id] := Set_Add_3545(locked_requests[piece->val->id], req);
        participant_votes[piece->val->id][req->id] := YES();
    }
    else
    {
        participant_votes[piece->val->id][req->id] := NO();
    }
  **** end structured program */

  anon0:
    goto anon3_Then, anon3_Else;

  anon3_Else:
    assume {:partition} !NoOverlap(locked_requests[piece->val->id], req->duration);
    participant_votes[piece->val->id][req->id] := NO();
    return;

  anon3_Then:
    assume {:partition} NoOverlap(locked_requests[piece->val->id], req->duration);
    locked_requests[piece->val->id] := Set_Add_3545(locked_requests[piece->val->id], req);
    participant_votes[piece->val->id][req->id] := YES();
    return;
}



procedure ADD_TO_COMMITTED_REQUESTS_GateSufficiencyChecker(req: Request);
  requires (forall pid: int :: 
    1 <= pid && pid <= NumParticipants
       ==> Set_Contains_3555(locked_requests[pid], req));
  requires !Set_Contains_3555(committed_requests, req);
  modifies committed_requests;



implementation ADD_TO_COMMITTED_REQUESTS_GateSufficiencyChecker(req: Request)
{
  /*** structured program:
    committed_requests := Set_Add_3545(committed_requests, req);
  **** end structured program */

  anon0:
    committed_requests := Set_Add_3545(committed_requests, req);
    return;
}



implementation voting(req: Request, piece: One_5506)
{
  /*** structured program:
    if (NoOverlap(locked_requests[piece->val->id], req->duration))
    {
        locked_requests[piece->val->id] := Set_Add_3545(locked_requests[piece->val->id], req);
        participant_votes[piece->val->id][req->id] := YES();
    }
    else
    {
        participant_votes[piece->val->id][req->id] := NO();
    }
  **** end structured program */

  anon0:
    goto anon3_Then, anon3_Else;

  anon3_Else:
    assume {:partition} !NoOverlap(locked_requests[piece->val->id], req->duration);
    participant_votes[piece->val->id][req->id] := NO();
    return;

  anon3_Then:
    assume {:partition} NoOverlap(locked_requests[piece->val->id], req->duration);
    locked_requests[piece->val->id] := Set_Add_3545(locked_requests[piece->val->id], req);
    participant_votes[piece->val->id][req->id] := YES();
    return;
}



procedure {:inline 1} voting(req: Request, piece: One_5506);
  modifies locked_requests, participant_votes;



function {:inline} Civl_InputOutputRelation_voting(req: Request, piece: One_5506) : bool
{
  (exists Civl_old_locked_requests: [int]Set_4510, 
      Civl_old_participant_votes: [int][ReqId]Vote, 
      Civl_old_committed_requests: Set_4510, 
      Civl_locked_requests: [int]Set_4510, 
      Civl_participant_votes: [int][ReqId]Vote, 
      Civl_committed_requests: Set_4510 :: 
    IsValidParticipantPiece(piece->val)
       && piece->val->val == req->id
       && Civl_old_participant_votes[piece->val->id][piece->val->val] == NULL()
       && ((
          NoOverlap(Civl_old_locked_requests[piece->val->id], req->duration)
           && Civl_locked_requests
             == Civl_old_locked_requests[piece->val->id := Set_Add_3545(Civl_old_locked_requests[piece->val->id], req)]
           && Civl_participant_votes
             == Civl_old_participant_votes[piece->val->id := Civl_old_participant_votes[piece->val->id][req->id := YES()]])
         || (
          !NoOverlap(Civl_locked_requests[piece->val->id], req->duration)
           && Civl_participant_votes
             == Civl_old_participant_votes[piece->val->id := Civl_old_participant_votes[piece->val->id][req->id := NO()]]
           && Civl_locked_requests == Civl_old_locked_requests)))
}

implementation ADD_TO_COMMITTED_REQUESTS(req: Request)
{
  /*** structured program:
    committed_requests := Set_Add_3545(committed_requests, req);
  **** end structured program */

  anon0:
    committed_requests := Set_Add_3545(committed_requests, req);
    return;
}



procedure {:inline 1} ADD_TO_COMMITTED_REQUESTS(req: Request);
  modifies committed_requests;



function {:inline} Civl_InputOutputRelation_ADD_TO_COMMITTED_REQUESTS(req: Request) : bool
{
  (exists Civl_old_locked_requests: [int]Set_4510, 
      Civl_old_participant_votes: [int][ReqId]Vote, 
      Civl_old_committed_requests: Set_4510, 
      Civl_locked_requests: [int]Set_4510, 
      Civl_participant_votes: [int][ReqId]Vote, 
      Civl_committed_requests: Set_4510 :: 
    (forall pid: int :: 
        1 <= pid && pid <= NumParticipants
           ==> Set_Contains_3555(Civl_old_locked_requests[pid], req))
       && !Set_Contains_3555(Civl_old_committed_requests, req)
       && Civl_committed_requests == Set_Add_3545(Civl_old_committed_requests, req))
}

implementation RECEIVE_VOTE(pid: int, reqId: ReqId) returns (v: Vote)
{
  /*** structured program:
    assume participant_votes[pid][reqId] != NULL();
    v := participant_votes[pid][reqId];
  **** end structured program */

  anon0:
    assume participant_votes[pid][reqId] != NULL();
    v := participant_votes[pid][reqId];
    return;
}



procedure {:inline 1} RECEIVE_VOTE(pid: int, reqId: ReqId) returns (v: Vote);



function {:inline} Civl_InputOutputRelation_RECEIVE_VOTE(pid: int, reqId: ReqId, v: Vote) : bool
{
  (exists Civl_old_locked_requests: [int]Set_4510, 
      Civl_old_participant_votes: [int][ReqId]Vote, 
      Civl_old_committed_requests: Set_4510, 
      Civl_locked_requests: [int]Set_4510, 
      Civl_participant_votes: [int][ReqId]Vote, 
      Civl_committed_requests: Set_4510 :: 
    Civl_participant_votes[pid][reqId] != NULL()
       && v == Civl_participant_votes[pid][reqId])
}

implementation WAIT_FOR_PARTICIPANT_VOTE(reqId: ReqId)
{
  /*** structured program:
    assume (forall pid: int :: 
      1 <= pid && pid <= NumParticipants ==> participant_votes[pid][reqId] != NULL());
  **** end structured program */

  anon0:
    assume (forall pid: int :: 
      1 <= pid && pid <= NumParticipants ==> participant_votes[pid][reqId] != NULL());
    return;
}



procedure {:inline 1} WAIT_FOR_PARTICIPANT_VOTE(reqId: ReqId);



function {:inline} Civl_InputOutputRelation_WAIT_FOR_PARTICIPANT_VOTE(reqId: ReqId) : bool
{
  (exists Civl_old_locked_requests: [int]Set_4510, 
      Civl_old_participant_votes: [int][ReqId]Vote, 
      Civl_old_committed_requests: Set_4510, 
      Civl_locked_requests: [int]Set_4510, 
      Civl_participant_votes: [int][ReqId]Vote, 
      Civl_committed_requests: Set_4510 :: 
    (forall pid: int :: 
      1 <= pid && pid <= NumParticipants
         ==> Civl_participant_votes[pid][reqId] != NULL()))
}

implementation Civl_Skip()
{

  init:
    return;
}



pure procedure {:inline 1} Civl_Skip();



function {:inline} Civl_InputOutputRelation_Civl_Skip() : bool
{
  (exists Civl_old_locked_requests: [int]Set_4510, 
      Civl_old_participant_votes: [int][ReqId]Vote, 
      Civl_old_committed_requests: Set_4510, 
      Civl_locked_requests: [int]Set_4510, 
      Civl_participant_votes: [int][ReqId]Vote, 
      Civl_committed_requests: Set_4510 :: 
    true)
}

implementation Civl_CommutativityChecker_RECEIVE_VOTE_voting(first_pid: int, first_reqId: ReqId, second_req: Request, second_piece: One_5506)
   returns (first_v: Vote)
{

  init:
    call first_v := RECEIVE_VOTE(first_pid, first_reqId);
    call voting(second_req, second_piece);
    assert true
       ==> (
          NoOverlap(old(locked_requests)[second_piece->val->id], second_req->duration)
           && participant_votes[first_pid][first_reqId] != NULL()
           && locked_requests
             == old(locked_requests)[second_piece->val->id := Set_Add_3545(old(locked_requests)[second_piece->val->id], second_req)]
           && participant_votes
             == old(participant_votes)[second_piece->val->id := old(participant_votes)[second_piece->val->id][second_req->id := YES()]]
           && first_v == participant_votes[first_pid][first_reqId])
         || (
          !NoOverlap(locked_requests[second_piece->val->id], second_req->duration)
           && participant_votes[first_pid][first_reqId] != NULL()
           && participant_votes
             == old(participant_votes)[second_piece->val->id := old(participant_votes)[second_piece->val->id][second_req->id := NO()]]
           && first_v == participant_votes[first_pid][first_reqId]
           && locked_requests == old(locked_requests));
    return;
}



procedure Civl_CommutativityChecker_RECEIVE_VOTE_voting(first_pid: int, first_reqId: ReqId, second_req: Request, second_piece: One_5506)
   returns (first_v: Vote);
  requires true;
  requires IsValidParticipantPiece(second_piece->val)
     && second_piece->val->val == second_req->id;
  requires participant_votes[second_piece->val->id][second_piece->val->val] == NULL();
  modifies locked_requests, participant_votes, committed_requests;



procedure Civl_coordinator_1(pieces: Set_5915, req: Request);
  requires pieces == AllParticipantPieces(req->id);
  requires (forall p: Fraction_4429_14 :: 
    Set_Contains_6188(pieces, p) ==> participant_votes[p->id][p->val] == NULL());
  requires (forall pid: int, req: Request :: 
    Set_Contains_14(ParticipantIds(), pid)
         && Set_Contains_3555(locked_requests[pid], req)
       ==> participant_votes[pid][req->id] == YES());
  requires (forall pid: int, req: Request :: 
    Set_Contains_14(ParticipantIds(), pid)
         && participant_votes[pid][req->id] == YES()
       ==> Set_Contains_3555(locked_requests[pid], req));
  requires !(exists pid: int, req1: Request, req2: Request :: 
    req1->id != req2->id
       && req1->duration == req2->duration
       && Set_Contains_3555(locked_requests[pid], req1)
       && Set_Contains_3555(locked_requests[pid], req2));
  requires !(exists req1: Request, req2: Request :: 
    req1->id != req2->id
       && req1->duration == req2->duration
       && Set_Contains_3555(committed_requests, req1)
       && Set_Contains_3555(committed_requests, req2));
  requires (forall req: Request :: 
    Set_Contains_3555(committed_requests, req)
       ==> (forall pid: int :: 
        1 <= pid && pid <= NumParticipants
           ==> Set_Contains_3555(locked_requests[pid], req)));
  modifies locked_requests, participant_votes, committed_requests;



procedure Civl_voting0_1(req: Request, piece: One_5506);
  requires IsValidParticipantPiece(piece->val) && piece->val->val == req->id;
  requires participant_votes[piece->val->id][piece->val->val] == NULL();
  modifies locked_requests, participant_votes, committed_requests;



implementation Civl_coordinator_1(pieces: Set_5915, req: Request)
{
  var i: int;
  var j: int;
  var d: Decision;
  var v: Vote;
  var pieces': Set_5915;
  var piece: One_5506;
  var Civl_global_old_locked_requests: [int]Set_4510;
  var Civl_global_old_participant_votes: [int][ReqId]Vote;
  var Civl_global_old_committed_requests: Set_4510;
  var Civl_pc: bool;
  var Civl_ok: bool;
  var Civl_eval: bool;
  var Civl_linear_Request_available: [Request]bool;
  var Civl_linear_Fraction_4429_14_available: [Fraction_4429_14]bool;
  var Civl_linear_int_available: [int]bool;

  /*** structured program:
    pieces' := pieces;
    d := COMMIT();
    j := 1;
    while (j <= NumParticipants)
      invariant 1 <= j && j <= NumParticipants + 1;
      invariant pieces' == JParticipantPieces(req->id, j);
    {
        call piece := One_Get(pieces', Fraction(req->id, j, ParticipantIds()));
        assert participant_votes[piece->val->id][piece->val->val] == NULL();
        async call voting0(req, piece);
        j := j + 1;
    }

    i := 1;
    call YieldBig();
    while (i <= NumParticipants)
      invariant 1 <= i && i <= NumParticipants + 1;
      invariant d != ABORT()
         ==> (forall k: int :: 
          1 <= k && k <= i - 1 ==> participant_votes[k][req->id] == YES());
    {
        call v := receive_vote(i, req->id);
        if (v == NO())
        {
            d := ABORT();
        }

        i := i + 1;
    }

    if (d == COMMIT())
    {
        assert (forall p: int :: 
          1 <= p && p <= NumParticipants ==> participant_votes[p][req->id] == YES());
        assert (forall pid: int :: 
          1 <= pid && pid <= NumParticipants
             ==> Set_Contains_3555(locked_requests[pid], req));
        assert !(exists pid: int, req1: Request, req2: Request :: 
          req1->id != req2->id
             && req1->duration == req2->duration
             && Set_Contains_3555(locked_requests[pid], req1)
             && Set_Contains_3555(locked_requests[pid], req2));
        assert (forall req: Request :: 
          Set_Contains_3555(committed_requests, req)
             ==> (forall pid: int :: 
              1 <= pid && pid <= NumParticipants
                 ==> Set_Contains_3555(locked_requests[pid], req)));
        assert !Set_Contains_3555(committed_requests, req);
        call add_to_committed_requests(req);
    }
  **** end structured program */

  Civl_init:
    havoc locked_requests, participant_votes, committed_requests;
    assume old(pieces) == AllParticipantPieces(old(req)->id);
    assume (forall p: Fraction_4429_14 :: 
      Set_Contains_6188(old(pieces), p) ==> participant_votes[p->id][p->val] == NULL());
    assume (forall pid: int, req: Request :: 
      Set_Contains_14(ParticipantIds(), pid)
           && Set_Contains_3555(locked_requests[pid], req)
         ==> participant_votes[pid][req->id] == YES());
    assume (forall pid: int, req: Request :: 
      Set_Contains_14(ParticipantIds(), pid)
           && participant_votes[pid][req->id] == YES()
         ==> Set_Contains_3555(locked_requests[pid], req));
    assume !(exists pid: int, req1: Request, req2: Request :: 
      req1->id != req2->id
         && req1->duration == req2->duration
         && Set_Contains_3555(locked_requests[pid], req1)
         && Set_Contains_3555(locked_requests[pid], req2));
    assume !(exists req1: Request, req2: Request :: 
      req1->id != req2->id
         && req1->duration == req2->duration
         && Set_Contains_3555(committed_requests, req1)
         && Set_Contains_3555(committed_requests, req2));
    assume (forall req: Request :: 
      Set_Contains_3555(committed_requests, req)
         ==> (forall pid: int :: 
          1 <= pid && pid <= NumParticipants
             ==> Set_Contains_3555(locked_requests[pid], req)));
    Civl_global_old_locked_requests, Civl_global_old_participant_votes, Civl_global_old_committed_requests := locked_requests, participant_votes, committed_requests;
    Civl_pc, Civl_ok, Civl_eval := false, false, false;
    assume true;
    Civl_linear_Request_available, Civl_linear_Fraction_4429_14_available, Civl_linear_int_available := MapConst_5_4510(false), MapOr_5506(Set_Collector_5915(pieces), MapConst_5_5506(false)), MapConst_5_1711(false);
    goto anon0;

  anon0:
    pieces' := pieces;
    d := COMMIT();
    j := 1;
    goto anon8_LoopHead;

  anon8_LoopHead:
    assert 1 <= j && j <= NumParticipants + 1;
    assert pieces' == JParticipantPieces(req->id, j);
    goto anon8_LoopDone, anon8_LoopBody;

  anon8_LoopBody:
    assume {:partition} j <= NumParticipants;
    assert Set_Contains_6188(pieces', Fraction_4429_14(req->id, j, ParticipantIds()));
    pieces' := Set_Remove_6622(pieces', Fraction_4429_14(req->id, j, ParticipantIds()));
    piece := One_5506(Fraction_4429_14(req->id, j, ParticipantIds()));
    assert participant_votes[piece->val->id][piece->val->val] == NULL();
    call Civl_AsyncCall_voting0_1(req, piece);
    j := j + 1;
    goto anon8_LoopHead;

  anon8_LoopDone:
    assume {:partition} NumParticipants < j;
    goto anon2;

  anon2:
    i := 1;
    Civl_eval := true;
    goto anon2_0, Civl_NoninterferenceChecker, Civl_RefinementChecker;

  anon2_0:
    Civl_pc, Civl_ok := true ==> Civl_pc, Civl_eval || Civl_ok;
    call Civl_ParallelCall_YieldBig_1();
    assume Civl_pc || true;
    Civl_global_old_locked_requests, Civl_global_old_participant_votes, Civl_global_old_committed_requests := locked_requests, participant_votes, committed_requests;
    Civl_linear_Request_available, Civl_linear_Fraction_4429_14_available, Civl_linear_int_available := MapConst_5_4510(false), MapOr_5506(Set_Collector_5915(pieces'), MapConst_5_5506(false)), MapConst_5_1711(false);
    goto anon9_LoopHead;

  anon9_LoopHead:
    assert 1 <= i && i <= NumParticipants + 1;
    assert d != ABORT()
       ==> (forall k: int :: 
        1 <= k && k <= i - 1 ==> participant_votes[k][req->id] == YES());
    goto anon9_LoopDone, anon9_LoopBody;

  anon9_LoopBody:
    assume {:partition} i <= NumParticipants;
    call v := RECEIVE_VOTE(i, req->id);
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
    assume {:partition} NumParticipants < i;
    goto anon6;

  anon6:
    goto anon11_Then, anon11_Else;

  anon11_Else:
    assume {:partition} d != COMMIT();
    goto Civl_ReturnChecker, Civl_UnifiedReturn, Civl_NoninterferenceChecker;

  anon11_Then:
    assume {:partition} d == COMMIT();
    assert (forall p: int :: 
      1 <= p && p <= NumParticipants ==> participant_votes[p][req->id] == YES());
    assert (forall pid: int :: 
      1 <= pid && pid <= NumParticipants
         ==> Set_Contains_3555(locked_requests[pid], req));
    assert !(exists pid: int, req1: Request, req2: Request :: 
      req1->id != req2->id
         && req1->duration == req2->duration
         && Set_Contains_3555(locked_requests[pid], req1)
         && Set_Contains_3555(locked_requests[pid], req2));
    assert (forall req: Request :: 
      Set_Contains_3555(committed_requests, req)
         ==> (forall pid: int :: 
          1 <= pid && pid <= NumParticipants
             ==> Set_Contains_3555(locked_requests[pid], req)));
    assert !Set_Contains_3555(committed_requests, req);
    // <<< injected gate
    assert (forall pid: int :: 
      1 <= pid && pid <= NumParticipants
         ==> Set_Contains_3555(locked_requests[pid], req));
    assert !Set_Contains_3555(committed_requests, req);
    // injected gate >>>
    call ADD_TO_COMMITTED_REQUESTS(req);
    goto Civl_ReturnChecker, Civl_UnifiedReturn, Civl_NoninterferenceChecker;

  Civl_NoninterferenceChecker:
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Request_available, Civl_linear_Fraction_4429_14_available, Civl_linear_int_available, Civl_global_old_locked_requests, Civl_global_old_participant_votes, Civl_global_old_committed_requests);
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



implementation Civl_voting0_1(req: Request, piece: One_5506)
{
  var Civl_global_old_locked_requests: [int]Set_4510;
  var Civl_global_old_participant_votes: [int][ReqId]Vote;
  var Civl_global_old_committed_requests: Set_4510;
  var Civl_pc: bool;
  var Civl_ok: bool;
  var Civl_eval: bool;
  var Civl_linear_Request_available: [Request]bool;
  var Civl_linear_Fraction_4429_14_available: [Fraction_4429_14]bool;
  var Civl_linear_int_available: [int]bool;

  /*** structured program:
    call voting1(req, piece);
  **** end structured program */

  Civl_init:
    havoc locked_requests, participant_votes, committed_requests;
    assume IsValidParticipantPiece(old(piece)->val) && old(piece)->val->val == old(req)->id;
    assume participant_votes[old(piece)->val->id][old(piece)->val->val] == NULL();
    Civl_global_old_locked_requests, Civl_global_old_participant_votes, Civl_global_old_committed_requests := locked_requests, participant_votes, committed_requests;
    Civl_pc, Civl_ok, Civl_eval := false, false, false;
    assume true;
    Civl_linear_Request_available, Civl_linear_Fraction_4429_14_available, Civl_linear_int_available := MapConst_5_4510(false), MapOr_5506(One_Collector_5506(piece), MapConst_5_5506(false)), MapConst_5_1711(false);
    goto anon0;

  anon0:
    // <<< injected gate
    assert IsValidParticipantPiece(piece->val) && piece->val->val == req->id;
    assert participant_votes[piece->val->id][piece->val->val] == NULL();
    // injected gate >>>
    call voting(req, piece);
    goto Civl_ReturnChecker, Civl_UnifiedReturn, Civl_NoninterferenceChecker;

  Civl_NoninterferenceChecker:
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Request_available, Civl_linear_Fraction_4429_14_available, Civl_linear_int_available, Civl_global_old_locked_requests, Civl_global_old_participant_votes, Civl_global_old_committed_requests);
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



procedure Civl_AsyncCall_voting0_1(req: Request, piece: One_5506);
  requires IsValidParticipantPiece(piece->val) && piece->val->val == req->id;
  requires participant_votes[piece->val->id][piece->val->val] == NULL();



procedure {:inline 1} Civl_NoninterferenceChecker_yield_YieldBig(Civl_linear_Request_in: [Request]bool, 
    Civl_linear_Fraction_4429_14_in: [Fraction_4429_14]bool, 
    Civl_linear_int_in: [int]bool, 
    Civl_snapshot_locked_requests: [int]Set_4510, 
    Civl_snapshot_participant_votes: [int][ReqId]Vote, 
    Civl_snapshot_committed_requests: Set_4510);



implementation Civl_NoninterferenceChecker_yield_YieldBig(Civl_linear_Request_in: [Request]bool, 
    Civl_linear_Fraction_4429_14_in: [Fraction_4429_14]bool, 
    Civl_linear_int_in: [int]bool, 
    Civl_snapshot_locked_requests: [int]Set_4510, 
    Civl_snapshot_participant_votes: [int][ReqId]Vote, 
    Civl_snapshot_committed_requests: Set_4510)
{

  enter:
    goto exit, L;

  exit:
    return;

  L:
    assume (forall pid: int, req: Request :: 
      Set_Contains_14(ParticipantIds(), pid)
           && Set_Contains_3555(Civl_snapshot_locked_requests[pid], req)
         ==> Civl_snapshot_participant_votes[pid][req->id] == YES());
    assume (forall pid: int, req: Request :: 
      Set_Contains_14(ParticipantIds(), pid)
           && Civl_snapshot_participant_votes[pid][req->id] == YES()
         ==> Set_Contains_3555(Civl_snapshot_locked_requests[pid], req));
    assume !(exists pid: int, req1: Request, req2: Request :: 
      req1->id != req2->id
         && req1->duration == req2->duration
         && Set_Contains_3555(Civl_snapshot_locked_requests[pid], req1)
         && Set_Contains_3555(Civl_snapshot_locked_requests[pid], req2));
    assume !(exists req1: Request, req2: Request :: 
      req1->id != req2->id
         && req1->duration == req2->duration
         && Set_Contains_3555(Civl_snapshot_committed_requests, req1)
         && Set_Contains_3555(Civl_snapshot_committed_requests, req2));
    assume (forall req: Request :: 
      Set_Contains_3555(Civl_snapshot_committed_requests, req)
         ==> (forall pid: int :: 
          1 <= pid && pid <= NumParticipants
             ==> Set_Contains_3555(Civl_snapshot_locked_requests[pid], req)));
    assert (forall pid: int, req: Request :: 
      Set_Contains_14(ParticipantIds(), pid)
           && Set_Contains_3555(locked_requests[pid], req)
         ==> participant_votes[pid][req->id] == YES());
    assert (forall pid: int, req: Request :: 
      Set_Contains_14(ParticipantIds(), pid)
           && participant_votes[pid][req->id] == YES()
         ==> Set_Contains_3555(locked_requests[pid], req));
    assert !(exists pid: int, req1: Request, req2: Request :: 
      req1->id != req2->id
         && req1->duration == req2->duration
         && Set_Contains_3555(locked_requests[pid], req1)
         && Set_Contains_3555(locked_requests[pid], req2));
    assert !(exists req1: Request, req2: Request :: 
      req1->id != req2->id
         && req1->duration == req2->duration
         && Set_Contains_3555(committed_requests, req1)
         && Set_Contains_3555(committed_requests, req2));
    assert (forall req: Request :: 
      Set_Contains_3555(committed_requests, req)
         ==> (forall pid: int :: 
          1 <= pid && pid <= NumParticipants
             ==> Set_Contains_3555(locked_requests[pid], req)));
    assume false;
    return;
}



procedure {:inline 1} Civl_NoninterferenceChecker_yield_YieldVoting(Civl_linear_Request_in: [Request]bool, 
    Civl_linear_Fraction_4429_14_in: [Fraction_4429_14]bool, 
    Civl_linear_int_in: [int]bool, 
    Civl_snapshot_locked_requests: [int]Set_4510, 
    Civl_snapshot_participant_votes: [int][ReqId]Vote, 
    Civl_snapshot_committed_requests: Set_4510);



implementation Civl_NoninterferenceChecker_yield_YieldVoting(Civl_linear_Request_in: [Request]bool, 
    Civl_linear_Fraction_4429_14_in: [Fraction_4429_14]bool, 
    Civl_linear_int_in: [int]bool, 
    Civl_snapshot_locked_requests: [int]Set_4510, 
    Civl_snapshot_participant_votes: [int][ReqId]Vote, 
    Civl_snapshot_committed_requests: Set_4510)
{
  var piece: One_5506;
  var req: Request;

  enter:
    goto exit, L;

  exit:
    return;

  L:
    assume (exists Civl_partition_Fraction_4429_14: [Fraction_4429_14]int :: 
      MapImp_5506(One_Collector_5506(piece), 
            MapEq_5506_3(Civl_partition_Fraction_4429_14, MapConst_3_5506(0)))
           == MapConst_5_5506(true)
         && MapImp_5506(Civl_linear_Fraction_4429_14_in, 
            MapEq_5506_3(Civl_partition_Fraction_4429_14, MapConst_3_5506(1)))
           == MapConst_5_5506(true));
    assume IsValidParticipantPiece(piece->val) && piece->val->val == req->id;
    assume Civl_snapshot_participant_votes[piece->val->id][piece->val->val] == NULL();
    assert IsValidParticipantPiece(piece->val) && piece->val->val == req->id;
    assert participant_votes[piece->val->id][piece->val->val] == NULL();
    assume false;
    return;
}



procedure {:inline 1} Civl_NoninterferenceChecker_yield_YieldInit(Civl_linear_Request_in: [Request]bool, 
    Civl_linear_Fraction_4429_14_in: [Fraction_4429_14]bool, 
    Civl_linear_int_in: [int]bool, 
    Civl_snapshot_locked_requests: [int]Set_4510, 
    Civl_snapshot_participant_votes: [int][ReqId]Vote, 
    Civl_snapshot_committed_requests: Set_4510);



implementation Civl_NoninterferenceChecker_yield_YieldInit(Civl_linear_Request_in: [Request]bool, 
    Civl_linear_Fraction_4429_14_in: [Fraction_4429_14]bool, 
    Civl_linear_int_in: [int]bool, 
    Civl_snapshot_locked_requests: [int]Set_4510, 
    Civl_snapshot_participant_votes: [int][ReqId]Vote, 
    Civl_snapshot_committed_requests: Set_4510)
{
  var pieces: Set_5915;
  var req: Request;

  enter:
    goto exit, L;

  exit:
    return;

  L:
    assume (exists Civl_partition_Fraction_4429_14: [Fraction_4429_14]int :: 
      MapImp_5506(Set_Collector_5915(pieces), 
            MapEq_5506_3(Civl_partition_Fraction_4429_14, MapConst_3_5506(0)))
           == MapConst_5_5506(true)
         && MapImp_5506(Civl_linear_Fraction_4429_14_in, 
            MapEq_5506_3(Civl_partition_Fraction_4429_14, MapConst_3_5506(1)))
           == MapConst_5_5506(true));
    assume pieces == AllParticipantPieces(req->id);
    assume (forall p: Fraction_4429_14 :: 
      Set_Contains_6188(pieces, p)
         ==> Civl_snapshot_participant_votes[p->id][p->val] == NULL());
    assert pieces == AllParticipantPieces(req->id);
    assert (forall p: Fraction_4429_14 :: 
      Set_Contains_6188(pieces, p) ==> participant_votes[p->id][p->val] == NULL());
    assume false;
    return;
}



procedure {:inline 1} Civl_NoninterferenceChecker_yield_YieldTrue(Civl_linear_Request_in: [Request]bool, 
    Civl_linear_Fraction_4429_14_in: [Fraction_4429_14]bool, 
    Civl_linear_int_in: [int]bool, 
    Civl_snapshot_locked_requests: [int]Set_4510, 
    Civl_snapshot_participant_votes: [int][ReqId]Vote, 
    Civl_snapshot_committed_requests: Set_4510);



implementation Civl_NoninterferenceChecker_yield_YieldTrue(Civl_linear_Request_in: [Request]bool, 
    Civl_linear_Fraction_4429_14_in: [Fraction_4429_14]bool, 
    Civl_linear_int_in: [int]bool, 
    Civl_snapshot_locked_requests: [int]Set_4510, 
    Civl_snapshot_participant_votes: [int][ReqId]Vote, 
    Civl_snapshot_committed_requests: Set_4510)
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



procedure Civl_ParallelCall_YieldBig_1();
  requires (forall pid: int, req: Request :: 
    Set_Contains_14(ParticipantIds(), pid)
         && Set_Contains_3555(locked_requests[pid], req)
       ==> participant_votes[pid][req->id] == YES());
  requires (forall pid: int, req: Request :: 
    Set_Contains_14(ParticipantIds(), pid)
         && participant_votes[pid][req->id] == YES()
       ==> Set_Contains_3555(locked_requests[pid], req));
  requires !(exists pid: int, req1: Request, req2: Request :: 
    req1->id != req2->id
       && req1->duration == req2->duration
       && Set_Contains_3555(locked_requests[pid], req1)
       && Set_Contains_3555(locked_requests[pid], req2));
  requires !(exists req1: Request, req2: Request :: 
    req1->id != req2->id
       && req1->duration == req2->duration
       && Set_Contains_3555(committed_requests, req1)
       && Set_Contains_3555(committed_requests, req2));
  requires (forall req: Request :: 
    Set_Contains_3555(committed_requests, req)
       ==> (forall pid: int :: 
        1 <= pid && pid <= NumParticipants
           ==> Set_Contains_3555(locked_requests[pid], req)));
  modifies locked_requests, participant_votes, committed_requests;
  ensures (forall pid: int, req: Request :: 
    Set_Contains_14(ParticipantIds(), pid)
         && Set_Contains_3555(locked_requests[pid], req)
       ==> participant_votes[pid][req->id] == YES());
  ensures (forall pid: int, req: Request :: 
    Set_Contains_14(ParticipantIds(), pid)
         && participant_votes[pid][req->id] == YES()
       ==> Set_Contains_3555(locked_requests[pid], req));
  ensures !(exists pid: int, req1: Request, req2: Request :: 
    req1->id != req2->id
       && req1->duration == req2->duration
       && Set_Contains_3555(locked_requests[pid], req1)
       && Set_Contains_3555(locked_requests[pid], req2));
  ensures !(exists req1: Request, req2: Request :: 
    req1->id != req2->id
       && req1->duration == req2->duration
       && Set_Contains_3555(committed_requests, req1)
       && Set_Contains_3555(committed_requests, req2));
  ensures (forall req: Request :: 
    Set_Contains_3555(committed_requests, req)
       ==> (forall pid: int :: 
        1 <= pid && pid <= NumParticipants
           ==> Set_Contains_3555(locked_requests[pid], req)));



procedure Civl_PendingAsyncNoninterferenceChecker_voting_1(req: Request, piece: One_5506);
  requires IsValidParticipantPiece(piece->val) && piece->val->val == req->id;
  requires participant_votes[piece->val->id][piece->val->val] == NULL();
  modifies locked_requests, participant_votes, committed_requests;



implementation Civl_PendingAsyncNoninterferenceChecker_voting_1(req: Request, piece: One_5506)
{
  var Civl_global_old_locked_requests: [int]Set_4510;
  var Civl_global_old_participant_votes: [int][ReqId]Vote;
  var Civl_global_old_committed_requests: Set_4510;
  var Civl_linear_Request_available: [Request]bool;
  var Civl_linear_Fraction_4429_14_available: [Fraction_4429_14]bool;
  var Civl_linear_int_available: [int]bool;

  init:
    Civl_global_old_locked_requests, Civl_global_old_participant_votes, Civl_global_old_committed_requests := locked_requests, participant_votes, committed_requests;
    Civl_linear_Request_available, Civl_linear_Fraction_4429_14_available, Civl_linear_int_available := MapConst_5_4510(false), MapOr_5506(One_Collector_5506(piece), MapConst_5_5506(false)), MapConst_5_1711(false);
    call voting(req, piece);
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Request_available, Civl_linear_Fraction_4429_14_available, Civl_linear_int_available, Civl_global_old_locked_requests, Civl_global_old_participant_votes, Civl_global_old_committed_requests);
    return;
}



procedure {:inline 1} Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Request_in: [Request]bool, 
    Civl_linear_Fraction_4429_14_in: [Fraction_4429_14]bool, 
    Civl_linear_int_in: [int]bool, 
    Civl_global_old_locked_requests: [int]Set_4510, 
    Civl_global_old_participant_votes: [int][ReqId]Vote, 
    Civl_global_old_committed_requests: Set_4510);



implementation Civl_Wrapper_NoninterferenceChecker_1(Civl_Civl_linear_Request_in: [Request]bool, 
    Civl_Civl_linear_Fraction_4429_14_in: [Fraction_4429_14]bool, 
    Civl_Civl_linear_int_in: [int]bool, 
    Civl_Civl_global_old_locked_requests: [int]Set_4510, 
    Civl_Civl_global_old_participant_votes: [int][ReqId]Vote, 
    Civl_Civl_global_old_committed_requests: Set_4510)
{

  enter:
    goto L_0, L_1, L_2, L_3;

  L_0:
    call Civl_NoninterferenceChecker_yield_YieldBig(Civl_Civl_linear_Request_in, Civl_Civl_linear_Fraction_4429_14_in, Civl_Civl_linear_int_in, Civl_Civl_global_old_locked_requests, Civl_Civl_global_old_participant_votes, Civl_Civl_global_old_committed_requests);
    return;

  L_1:
    call Civl_NoninterferenceChecker_yield_YieldVoting(Civl_Civl_linear_Request_in, Civl_Civl_linear_Fraction_4429_14_in, Civl_Civl_linear_int_in, Civl_Civl_global_old_locked_requests, Civl_Civl_global_old_participant_votes, Civl_Civl_global_old_committed_requests);
    return;

  L_2:
    call Civl_NoninterferenceChecker_yield_YieldInit(Civl_Civl_linear_Request_in, Civl_Civl_linear_Fraction_4429_14_in, Civl_Civl_linear_int_in, Civl_Civl_global_old_locked_requests, Civl_Civl_global_old_participant_votes, Civl_Civl_global_old_committed_requests);
    return;

  L_3:
    call Civl_NoninterferenceChecker_yield_YieldTrue(Civl_Civl_linear_Request_in, Civl_Civl_linear_Fraction_4429_14_in, Civl_Civl_linear_int_in, Civl_Civl_global_old_locked_requests, Civl_Civl_global_old_participant_votes, Civl_Civl_global_old_committed_requests);
    return;
}


