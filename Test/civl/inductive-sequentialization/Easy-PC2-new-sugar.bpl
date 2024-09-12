// Boogie program verifier version 3.2.3.0, Copyright (c) 2003-2014, Microsoft.
// Command Line Options: Easy-PC2-new.bpl /trustMoverTypes /civlDesugaredFile:Easy-PC2-new-sugar.bpl

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

type ParticipantPiece = Fraction_3920_14;

const NumParticipants: int;

var locked_requests: [int]Set_3958;

var participant_votes: [int][ReqId]Vote;

var committed_requests: Set_3958;

function {:inline} NoOverlap(req_set: Set_3958, d: int) : bool
{
  !(exists req: Request :: Set_Contains_3128(req_set, req) && req->duration == d)
}

function {:inline} JParticipantIds(j: int) : Set_14
{
  Set_14((lambda {:pool "P1"} x: int :: j <= x && x <= NumParticipants))
}

function {:inline} JParticipantPieces(r: ReqId, j: int) : Set_4074
{
  Set_4074((lambda {:pool "P2"} x: Fraction_3920_14 :: 
      x->val == r
         && x->ids == ParticipantIds()
         && Set_Contains_14(JParticipantIds(j), x->id)))
}

function {:inline} AllParticipantPieces(r: ReqId) : Set_4074
{
  Set_4074((lambda {:pool "P2"} x: Fraction_3920_14 :: 
      x->val == r && x->ids == ParticipantIds() && Set_Contains_14(x->ids, x->id)))
}

function {:inline} ParticipantIds() : Set_14
{
  Set_14((lambda {:pool "P1"} x: int :: 1 <= x && x <= NumParticipants))
}

function {:inline} Init(fracs: Set_4074, participant_votes: [int][ReqId]Vote) : bool
{
  (forall p: Fraction_3920_14 :: 
    Set_Contains_4369(fracs, p) ==> participant_votes[p->id][p->val] == NULL())
}

datatype voting {
  voting(req: Request, piece: One_4770)
}

const Identity: [int]int;

function {:inline} AtLeast(x: int) : [int]bool
{
  MapLe_1286(MapConst_1303_1286(x), Identity)
}

function {:inline} Range(from: int, n: int) : [int]bool
{
  MapDiff_1306(AtLeast(from), AtLeast(from + n))
}

type {:builtin "Seq"} Seq _;

pure procedure Assume(b: bool);
  ensures b;



datatype Fraction_3920_14 {
  Fraction_3920_14(val: ReqId, id: int, ids: Set_14)
}

datatype Set_14 {
  Set_14(val: [int]bool)
}

datatype Set_3958 {
  Set_3958(val: [Request]bool)
}

function {:inline} Set_Contains_3128(a: Set_3958, t: Request) : bool
{
  a->val[t]
}

datatype Set_4074 {
  Set_4074(val: [Fraction_3920_14]bool)
}

function {:inline} Set_Contains_14(a: Set_14, t: int) : bool
{
  a->val[t]
}

function {:inline} Set_Contains_4369(a: Set_4074, t: Fraction_3920_14) : bool
{
  a->val[t]
}

datatype One_4770 {
  One_4770(val: Fraction_3920_14)
}

pure procedure One_Get_4901(path: Set_4074, k: Fraction_3920_14) returns (l: One_4770);



function {:inline} Set_Add_3118(a: Set_3958, t: Request) : Set_3958
{
  Set_3958(a->val[t := true])
}

function {:builtin "MapConst"} MapConst_1303_1286(int) : [int]int;

function {:builtin "MapLe"} MapLe_1286([int]int, [int]int) : [int]bool;

function {:inline} MapDiff_1306(a: [int]bool, b: [int]bool) : [int]bool
{
  MapAnd_1306(a, MapNot_1306(b))
}

function {:builtin "MapNot"} MapNot_1306([int]bool) : [int]bool;

function {:builtin "MapAnd"} MapAnd_1306([int]bool, [int]bool) : [int]bool;

datatype Vec_1303 {
  Vec_1303(contents: [int]int, len: int)
}

function Default_1303() : int;

function {:builtin "MapIte"} MapIte_1327_1303([int]bool, [int]int, [int]int) : [int]int;

function {:builtin "MapConst"} MapConst_5_1286(bool) : [int]bool;

function Choice_1286(a: [int]bool) : int;

datatype Vec_5 {
  Vec_5(contents: [int]bool, len: int)
}

function Default_5() : bool;

function {:builtin "MapIte"} MapIte_1327_5([int]bool, [int]bool, [int]bool) : [int]bool;

axiom NumParticipants > 0;

axiom (forall x: int :: Identity[x] == x);

axiom (forall x: Vec_5 :: 
  { x->len } { x->contents } 
  MapIte_1327_5(Range(0, x->len), MapConst_5_1286(Default_5()), x->contents)
     == MapConst_5_1286(Default_5()));

axiom (forall x: Vec_1303 :: 
  { x->len } { x->contents } 
  MapIte_1327_1303(Range(0, x->len), MapConst_1303_1286(Default_1303()), x->contents)
     == MapConst_1303_1286(Default_1303()));

axiom (forall x: Vec_5 :: { x->len } x->len >= 0);

axiom (forall x: Vec_1303 :: { x->len } x->len >= 0);

axiom (forall a: [int]bool :: 
  { Choice_1286(a) } 
  a == MapConst_5_1286(false) || a[Choice_1286(a)]);

function {:builtin "MapConst"} MapConst_5_3958(bool) : [Request]bool;

function {:builtin "MapConst"} MapConst_3_3958(int) : [Request]int;

function {:builtin "MapAnd"} MapAnd_3958([Request]bool, [Request]bool) : [Request]bool;

function {:builtin "MapOr"} MapOr_3958([Request]bool, [Request]bool) : [Request]bool;

function {:builtin "MapImp"} MapImp_3958([Request]bool, [Request]bool) : [Request]bool;

function {:builtin "MapEq"} MapEq_3958_3([Request]int, [Request]int) : [Request]bool;

function {:builtin "MapAdd"} MapAdd_3958([Request]int, [Request]int) : [Request]int;

function {:builtin "MapIte"} MapIte_3958_3([Request]bool, [Request]int, [Request]int) : [Request]int;

function {:builtin "MapLe"} MapLe_3958([Request]int, [Request]int) : [Request]bool;

function {:inline} Set_Collector_3958(a: Set_3958) : [Request]bool
{
  a->val
}

function {:builtin "MapOr"} MapOr_14([int]bool, [int]bool) : [int]bool;

function {:builtin "MapImp"} MapImp_14([int]bool, [int]bool) : [int]bool;

function {:builtin "MapEq"} MapEq_14_3([int]int, [int]int) : [int]bool;

function {:builtin "MapAdd"} MapAdd_14([int]int, [int]int) : [int]int;

function {:inline} Set_Collector_14(a: Set_14) : [int]bool
{
  a->val
}

function {:builtin "MapConst"} MapConst_5_4074(bool) : [Fraction_3920_14]bool;

function {:builtin "MapConst"} MapConst_3_4074(int) : [Fraction_3920_14]int;

function {:builtin "MapAnd"} MapAnd_4074([Fraction_3920_14]bool, [Fraction_3920_14]bool) : [Fraction_3920_14]bool;

function {:builtin "MapOr"} MapOr_4074([Fraction_3920_14]bool, [Fraction_3920_14]bool) : [Fraction_3920_14]bool;

function {:builtin "MapImp"} MapImp_4074([Fraction_3920_14]bool, [Fraction_3920_14]bool) : [Fraction_3920_14]bool;

function {:builtin "MapEq"} MapEq_4074_3([Fraction_3920_14]int, [Fraction_3920_14]int) : [Fraction_3920_14]bool;

function {:builtin "MapAdd"} MapAdd_4074([Fraction_3920_14]int, [Fraction_3920_14]int) : [Fraction_3920_14]int;

function {:builtin "MapIte"} MapIte_4074_3([Fraction_3920_14]bool, [Fraction_3920_14]int, [Fraction_3920_14]int)
   : [Fraction_3920_14]int;

function {:builtin "MapLe"} MapLe_4074([Fraction_3920_14]int, [Fraction_3920_14]int) : [Fraction_3920_14]bool;

function {:inline} Set_Collector_4074(a: Set_4074) : [Fraction_3920_14]bool
{
  a->val
}

function {:inline} One_Collector_4770(a: One_4770) : [Fraction_3920_14]bool
{
  MapOne_4770(a->val)
}

function {:inline} MapOne_4770(t: Fraction_3920_14) : [Fraction_3920_14]bool
{
  MapConst_5_4074(false)[t := true]
}

function {:builtin "MapAdd"} MapAdd_6929([voting]int, [voting]int) : [voting]int;

function {:builtin "MapConst"} MapConst_3_6940(int) : [voting]int;

function {:builtin "MapIte"} MapIte_6947_3([voting]bool, [voting]int, [voting]int) : [voting]int;

procedure ADD_TO_COMMITTED_REQUESTS_GateSufficiencyChecker(req: Request);
  requires !(exists req0: Request :: 
    Set_Contains_3128(committed_requests, req0) && req0->id == req->id);
  requires !(exists req1: Request :: 
    req1->id != req->id
       && req1->duration == req->duration
       && Set_Contains_3128(committed_requests, req1));
  modifies committed_requests;



implementation ADD_TO_COMMITTED_REQUESTS_GateSufficiencyChecker(req: Request)
{
  /*** structured program:
    committed_requests := Set_Add_3118(committed_requests, req);
  **** end structured program */

  anon0:
    committed_requests := Set_Add_3118(committed_requests, req);
    return;
}



implementation voting(req: Request, piece: One_4770)
{
  /*** structured program:
    if (NoOverlap(locked_requests[piece->val->id], req->duration))
    {
        locked_requests[piece->val->id] := Set_Add_3118(locked_requests[piece->val->id], req);
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
    locked_requests[piece->val->id] := Set_Add_3118(locked_requests[piece->val->id], req);
    participant_votes[piece->val->id][req->id] := YES();
    return;
}



procedure {:inline 1} voting(req: Request, piece: One_4770);
  modifies locked_requests, participant_votes;



function {:inline} Civl_InputOutputRelation_voting(req: Request, piece: One_4770) : bool
{
  (exists Civl_old_locked_requests: [int]Set_3958, 
      Civl_old_participant_votes: [int][ReqId]Vote, 
      Civl_old_committed_requests: Set_3958, 
      Civl_locked_requests: [int]Set_3958, 
      Civl_participant_votes: [int][ReqId]Vote, 
      Civl_committed_requests: Set_3958 :: 
    (
        NoOverlap(Civl_old_locked_requests[piece->val->id], req->duration)
         && Civl_locked_requests
           == Civl_old_locked_requests[piece->val->id := Set_Add_3118(Civl_old_locked_requests[piece->val->id], req)]
         && Civl_participant_votes
           == Civl_old_participant_votes[piece->val->id := Civl_old_participant_votes[piece->val->id][req->id := YES()]])
       || (
        !NoOverlap(Civl_locked_requests[piece->val->id], req->duration)
         && Civl_participant_votes
           == Civl_old_participant_votes[piece->val->id := Civl_old_participant_votes[piece->val->id][req->id := NO()]]
         && Civl_locked_requests == Civl_old_locked_requests))
}

implementation ADD_TO_COMMITTED_REQUESTS(req: Request)
{
  /*** structured program:
    committed_requests := Set_Add_3118(committed_requests, req);
  **** end structured program */

  anon0:
    committed_requests := Set_Add_3118(committed_requests, req);
    return;
}



procedure {:inline 1} ADD_TO_COMMITTED_REQUESTS(req: Request);
  modifies committed_requests;



function {:inline} Civl_InputOutputRelation_ADD_TO_COMMITTED_REQUESTS(req: Request) : bool
{
  (exists Civl_old_locked_requests: [int]Set_3958, 
      Civl_old_participant_votes: [int][ReqId]Vote, 
      Civl_old_committed_requests: Set_3958, 
      Civl_locked_requests: [int]Set_3958, 
      Civl_participant_votes: [int][ReqId]Vote, 
      Civl_committed_requests: Set_3958 :: 
    !(exists req0: Request :: 
        Set_Contains_3128(Civl_old_committed_requests, req0) && req0->id == req->id)
       && !(exists req1: Request :: 
        req1->id != req->id
           && req1->duration == req->duration
           && Set_Contains_3128(Civl_old_committed_requests, req1))
       && Civl_committed_requests == Set_Add_3118(Civl_old_committed_requests, req))
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
  (exists Civl_old_locked_requests: [int]Set_3958, 
      Civl_old_participant_votes: [int][ReqId]Vote, 
      Civl_old_committed_requests: Set_3958, 
      Civl_locked_requests: [int]Set_3958, 
      Civl_participant_votes: [int][ReqId]Vote, 
      Civl_committed_requests: Set_3958 :: 
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
  (exists Civl_old_locked_requests: [int]Set_3958, 
      Civl_old_participant_votes: [int][ReqId]Vote, 
      Civl_old_committed_requests: Set_3958, 
      Civl_locked_requests: [int]Set_3958, 
      Civl_participant_votes: [int][ReqId]Vote, 
      Civl_committed_requests: Set_3958 :: 
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
  (exists Civl_old_locked_requests: [int]Set_3958, 
      Civl_old_participant_votes: [int][ReqId]Vote, 
      Civl_old_committed_requests: Set_3958, 
      Civl_locked_requests: [int]Set_3958, 
      Civl_participant_votes: [int][ReqId]Vote, 
      Civl_committed_requests: Set_3958 :: 
    true)
}

procedure Civl_coordinator_1(pieces: Set_4074, req: Request);
  requires pieces == AllParticipantPieces(req->id);
  requires (forall p: Fraction_3920_14 :: 
    Set_Contains_4369(pieces, p) ==> participant_votes[p->id][p->val] == NULL());
  modifies locked_requests, participant_votes, committed_requests;



procedure Civl_voting0_1(req: Request, piece: One_4770);
  modifies locked_requests, participant_votes, committed_requests;



implementation Civl_coordinator_1(pieces: Set_4074, req: Request)
{
  var i: int;
  var j: int;
  var d: Decision;
  var v: Vote;
  var pieces': Set_4074;
  var piece: One_4770;
  var Civl_global_old_locked_requests: [int]Set_3958;
  var Civl_global_old_participant_votes: [int][ReqId]Vote;
  var Civl_global_old_committed_requests: Set_3958;
  var Civl_pc: bool;
  var Civl_ok: bool;
  var Civl_eval: bool;
  var Civl_linear_Request_available: [Request]bool;
  var Civl_linear_int_available: [int]bool;
  var Civl_linear_Fraction_3920_14_available: [Fraction_3920_14]bool;

  /*** structured program:
    pieces' := pieces;
    assume false;
    d := COMMIT();
    j := 1;
    while (j <= NumParticipants)
      invariant {:layer 1} 1 <= j && j <= NumParticipants + 1;
    {
        call piece := One_Get(pieces', Fraction(req->id, j, ParticipantIds()));
        async call voting0(req, piece);
        j := j + 1;
    }

    call YieldTrue();
    i := 1;
    while (i <= NumParticipants)
    {
        call v := receive_vote(i, req->id);
        if (v == NO())
        {
            d := ABORT();
        }

        i := i + 1;
    }

    call YieldTrue();
  **** end structured program */

  Civl_init:
    havoc locked_requests, participant_votes, committed_requests;
    assume old(pieces) == AllParticipantPieces(old(req)->id);
    assume (forall p: Fraction_3920_14 :: 
      Set_Contains_4369(old(pieces), p) ==> participant_votes[p->id][p->val] == NULL());
    Civl_global_old_locked_requests, Civl_global_old_participant_votes, Civl_global_old_committed_requests := locked_requests, participant_votes, committed_requests;
    Civl_pc, Civl_ok, Civl_eval := false, false, false;
    assume true;
    Civl_linear_Request_available, Civl_linear_int_available, Civl_linear_Fraction_3920_14_available := MapConst_5_3958(false), MapConst_5_1286(false), MapOr_4074(Set_Collector_4074(pieces), MapConst_5_4074(false));
    goto anon0;

  anon0:
    pieces' := pieces;
    assume false;
    d := COMMIT();
    j := 1;
    goto Civl_ReturnChecker, Civl_UnifiedReturn, Civl_NoninterferenceChecker;

  Civl_NoninterferenceChecker:
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Request_available, Civl_linear_int_available, Civl_linear_Fraction_3920_14_available, Civl_global_old_locked_requests, Civl_global_old_participant_votes, Civl_global_old_committed_requests);
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



implementation Civl_voting0_1(req: Request, piece: One_4770)
{
  var Civl_global_old_locked_requests: [int]Set_3958;
  var Civl_global_old_participant_votes: [int][ReqId]Vote;
  var Civl_global_old_committed_requests: Set_3958;
  var Civl_pc: bool;
  var Civl_ok: bool;
  var Civl_eval: bool;
  var Civl_linear_Request_available: [Request]bool;
  var Civl_linear_int_available: [int]bool;
  var Civl_linear_Fraction_3920_14_available: [Fraction_3920_14]bool;

  /*** structured program:
    call voting1(req, piece);
  **** end structured program */

  Civl_init:
    havoc locked_requests, participant_votes, committed_requests;
    Civl_global_old_locked_requests, Civl_global_old_participant_votes, Civl_global_old_committed_requests := locked_requests, participant_votes, committed_requests;
    Civl_pc, Civl_ok, Civl_eval := false, false, false;
    assume true;
    Civl_linear_Request_available, Civl_linear_int_available, Civl_linear_Fraction_3920_14_available := MapConst_5_3958(false), MapConst_5_1286(false), MapOr_4074(One_Collector_4770(piece), MapConst_5_4074(false));
    goto anon0;

  anon0:
    call voting(req, piece);
    goto Civl_ReturnChecker, Civl_UnifiedReturn, Civl_NoninterferenceChecker;

  Civl_NoninterferenceChecker:
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Request_available, Civl_linear_int_available, Civl_linear_Fraction_3920_14_available, Civl_global_old_locked_requests, Civl_global_old_participant_votes, Civl_global_old_committed_requests);
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



procedure {:inline 1} Civl_NoninterferenceChecker_yield_YieldInit(Civl_linear_Request_in: [Request]bool, 
    Civl_linear_int_in: [int]bool, 
    Civl_linear_Fraction_3920_14_in: [Fraction_3920_14]bool, 
    Civl_snapshot_locked_requests: [int]Set_3958, 
    Civl_snapshot_participant_votes: [int][ReqId]Vote, 
    Civl_snapshot_committed_requests: Set_3958);



implementation Civl_NoninterferenceChecker_yield_YieldInit(Civl_linear_Request_in: [Request]bool, 
    Civl_linear_int_in: [int]bool, 
    Civl_linear_Fraction_3920_14_in: [Fraction_3920_14]bool, 
    Civl_snapshot_locked_requests: [int]Set_3958, 
    Civl_snapshot_participant_votes: [int][ReqId]Vote, 
    Civl_snapshot_committed_requests: Set_3958)
{
  var pieces: Set_4074;
  var req: Request;

  enter:
    goto exit, L;

  exit:
    return;

  L:
    assume (exists Civl_partition_Fraction_3920_14: [Fraction_3920_14]int :: 
      MapImp_4074(Set_Collector_4074(pieces), 
            MapEq_4074_3(Civl_partition_Fraction_3920_14, MapConst_3_4074(0)))
           == MapConst_5_4074(true)
         && MapImp_4074(Civl_linear_Fraction_3920_14_in, 
            MapEq_4074_3(Civl_partition_Fraction_3920_14, MapConst_3_4074(1)))
           == MapConst_5_4074(true));
    assume pieces == AllParticipantPieces(req->id);
    assume (forall p: Fraction_3920_14 :: 
      Set_Contains_4369(pieces, p)
         ==> Civl_snapshot_participant_votes[p->id][p->val] == NULL());
    assert pieces == AllParticipantPieces(req->id);
    assert (forall p: Fraction_3920_14 :: 
      Set_Contains_4369(pieces, p) ==> participant_votes[p->id][p->val] == NULL());
    assume false;
    return;
}



procedure {:inline 1} Civl_NoninterferenceChecker_yield_YieldTrue(Civl_linear_Request_in: [Request]bool, 
    Civl_linear_int_in: [int]bool, 
    Civl_linear_Fraction_3920_14_in: [Fraction_3920_14]bool, 
    Civl_snapshot_locked_requests: [int]Set_3958, 
    Civl_snapshot_participant_votes: [int][ReqId]Vote, 
    Civl_snapshot_committed_requests: Set_3958);



implementation Civl_NoninterferenceChecker_yield_YieldTrue(Civl_linear_Request_in: [Request]bool, 
    Civl_linear_int_in: [int]bool, 
    Civl_linear_Fraction_3920_14_in: [Fraction_3920_14]bool, 
    Civl_snapshot_locked_requests: [int]Set_3958, 
    Civl_snapshot_participant_votes: [int][ReqId]Vote, 
    Civl_snapshot_committed_requests: Set_3958)
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



procedure Civl_PendingAsyncNoninterferenceChecker_voting_1(req: Request, piece: One_4770);
  modifies locked_requests, participant_votes, committed_requests;



implementation Civl_PendingAsyncNoninterferenceChecker_voting_1(req: Request, piece: One_4770)
{
  var Civl_global_old_locked_requests: [int]Set_3958;
  var Civl_global_old_participant_votes: [int][ReqId]Vote;
  var Civl_global_old_committed_requests: Set_3958;
  var Civl_linear_Request_available: [Request]bool;
  var Civl_linear_int_available: [int]bool;
  var Civl_linear_Fraction_3920_14_available: [Fraction_3920_14]bool;

  init:
    Civl_global_old_locked_requests, Civl_global_old_participant_votes, Civl_global_old_committed_requests := locked_requests, participant_votes, committed_requests;
    Civl_linear_Request_available, Civl_linear_int_available, Civl_linear_Fraction_3920_14_available := MapConst_5_3958(false), MapConst_5_1286(false), MapOr_4074(One_Collector_4770(piece), MapConst_5_4074(false));
    call voting(req, piece);
    call Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Request_available, Civl_linear_int_available, Civl_linear_Fraction_3920_14_available, Civl_global_old_locked_requests, Civl_global_old_participant_votes, Civl_global_old_committed_requests);
    return;
}



procedure {:inline 1} Civl_Wrapper_NoninterferenceChecker_1(Civl_linear_Request_in: [Request]bool, 
    Civl_linear_int_in: [int]bool, 
    Civl_linear_Fraction_3920_14_in: [Fraction_3920_14]bool, 
    Civl_global_old_locked_requests: [int]Set_3958, 
    Civl_global_old_participant_votes: [int][ReqId]Vote, 
    Civl_global_old_committed_requests: Set_3958);



implementation Civl_Wrapper_NoninterferenceChecker_1(Civl_Civl_linear_Request_in: [Request]bool, 
    Civl_Civl_linear_int_in: [int]bool, 
    Civl_Civl_linear_Fraction_3920_14_in: [Fraction_3920_14]bool, 
    Civl_Civl_global_old_locked_requests: [int]Set_3958, 
    Civl_Civl_global_old_participant_votes: [int][ReqId]Vote, 
    Civl_Civl_global_old_committed_requests: Set_3958)
{

  enter:
    goto L_0, L_1;

  L_0:
    call Civl_NoninterferenceChecker_yield_YieldInit(Civl_Civl_linear_Request_in, Civl_Civl_linear_int_in, Civl_Civl_linear_Fraction_3920_14_in, Civl_Civl_global_old_locked_requests, Civl_Civl_global_old_participant_votes, Civl_Civl_global_old_committed_requests);
    return;

  L_1:
    call Civl_NoninterferenceChecker_yield_YieldTrue(Civl_Civl_linear_Request_in, Civl_Civl_linear_int_in, Civl_Civl_linear_Fraction_3920_14_in, Civl_Civl_global_old_locked_requests, Civl_Civl_global_old_participant_votes, Civl_Civl_global_old_committed_requests);
    return;
}


