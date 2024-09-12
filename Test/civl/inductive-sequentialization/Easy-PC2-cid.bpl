// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Pid = int;
type Duration = int;
type ReqId;
type Cid;

datatype Vote { YES(), NO(), NULL() }

datatype Decision { COMMIT(), ABORT(), NONE() }



datatype Request { Request(id: ReqId, duration: Duration )}

type ParticipantPiece = Fraction ReqId Pid;

// 1, dur 3
// 1, dur 6 

// only reqId should be linear

const NumParticipants:int;
axiom NumParticipants > 0;
axiom !(exists req1: Request, req2:Request :: req1->id == req2->id && req1->duration != req2->duration);

var {:layer 0,1} locked_requests: [Pid](Set Request);
var {:layer 0,1} participant_votes: [Pid][ReqId]Vote;
var {:layer 0,1} committed_requests: [Cid](Set Request);



function {:inline} NoOverlap(req_set: (Set Request), req: Request) : bool
{
    !(exists req': Request :: Set_Contains(req_set, req') && (req'->duration == req->duration) )
    // !(exists req': Request :: Set_Contains(req_set, req') && (req'->duration == req->duration || req'->id == req->id) )
}

yield invariant {:layer 1} YieldBig({:linear} req: One Request, {:linear} cid: One Cid);
invariant (forall pid: Pid, req: Request :: (Set_Contains(ParticipantIds(), pid) && Set_Contains(locked_requests[pid], req)) ==> participant_votes[pid][req->id] == YES());
invariant (forall pid: Pid, req: Request :: (Set_Contains(ParticipantIds(), pid) && participant_votes[pid][req->id] == YES()) ==> Set_Contains(locked_requests[pid], req)); // (9, 1) 
invariant !(exists pid: Pid, req1: Request, req2: Request :: req1->id != req2->id && req1->duration == req2->duration && Set_Contains(locked_requests[pid], req1) && Set_Contains(locked_requests[pid], req2));
invariant {:layer 1} (forall req:Request ::  Set_Contains(committed_requests[cid->val], req)  ==> (forall pid: Pid :: (1 <= pid && pid <= NumParticipants) ==>  (Set_Contains(locked_requests[pid], req))));
invariant !(exists req1: Request, req2: Request :: req1->id != req2->id && req1->duration == req2->duration && Set_Contains(committed_requests[cid->val], req1) && Set_Contains(committed_requests[cid->val], req2));

// invariant !(exists req1: Request, req2: Request :: req1->id != req2->id && req1->duration == req2->duration && Set_Contains(committed_requests, req1) && Set_Contains(committed_requests, req2));
// invariant (forall req: Request, pid: Pid :: Set_Contains(committed_requests, req)  ==> Set_Contains(locked_requests[pid], req));
// invariant !(exists req1: Request, req2: Request :: req1->id != req2->id && req1->duration == req2->duration && Set_Contains(committed_requests, req1) && Set_Contains(committed_requests, req2));
// invariant (forall req:Request ::  Set_Contains(committed_requests, req)  ==> (forall pid: Pid :: (1 <= pid && pid <= NumParticipants) ==>  (Set_Contains(locked_requests[pid], req))));

// yield invariant {:layer 1} YieldVoting({:linear} piece: One ParticipantPiece);
// invariant !(exists req0:Request :: Set_Contains(locked_requests[piece->val->id], req0) && req0->id == piece->val->val);
// invariant participant_votes[piece->val->id][piece->val->val] == NULL();

yield invariant {:layer 1} YieldVoting({:linear} piece: One ParticipantPiece, req: Request);
// invariant !(exists req0:Request :: Set_Contains(locked_requests[piece->val->id], req0) && req0->id == piece->val->val);
invariant IsValidParticipantPiece(piece->val) && piece->val->val == req->id;
invariant participant_votes[piece->val->id][piece->val->val] == NULL();
invariant !Set_Contains(locked_requests[piece->val->id], req);



yield invariant {:layer 1} YieldInit({:linear} pieces: Set ParticipantPiece, {:linear} req: One Request, {:linear} cid: One Cid);
invariant pieces == AllParticipantPieces(req->val->id);
invariant (forall p: ParticipantPiece :: Set_Contains(pieces, p) ==> participant_votes[p->id][p->val] == NULL());
invariant (forall p: ParticipantPiece :: Set_Contains(pieces, p) ==> !Set_Contains(locked_requests[p->id], req->val));
invariant !(Set_Contains(committed_requests[cid->val], req->val));


function {:inline} JParticipantIds(j: int): Set Pid {
    Set((lambda {:pool "P1"} x: int :: j <= x && x <= NumParticipants))
}

function {:inline} JParticipantPieces(r: ReqId, j: int): Set ParticipantPiece {
    Set((lambda {:pool "P2"} x: ParticipantPiece :: x->val == r && x->ids == ParticipantIds() && Set_Contains(JParticipantIds(j), x->id)))
}

function {:inline} AllParticipantPieces(r: ReqId): Set ParticipantPiece {
    Set((lambda {:pool "P2"} x: ParticipantPiece :: x->val == r && x->ids == ParticipantIds() && Set_Contains(x->ids, x->id)))
}
function {:inline} ParticipantIds(): Set Pid {
    Set((lambda {:pool "P1"} x: int :: 1 <= x && x <= NumParticipants))
}

function {:inline} IsValidParticipantPiece(x: ParticipantPiece): bool {
    x->ids == ParticipantIds() && Set_Contains(x->ids, x->id)
}
// Fraction1 : (val1, id1, ids1)
// Fraction2 : (val2, id2, ids2)

//   pids == MapConst(true) &&
//   RequestChannel == (lambda i:int :: 0) &&
//   VoteChannel == (lambda v:vote :: 0) &&
//   DecisionChannel == (lambda i:int :: (lambda d:decision :: 0)) &&
//   decisions == (lambda i:int :: NONE())


yield invariant {:layer 1} YieldTrue();
invariant true;


yield procedure {:layer 1} coordinator({:linear_in} cid: One Cid, {:linear_in} pieces: Set ParticipantPiece,  {:linear_in} req: One Request) // (1, 3) (1, 6) 
requires call YieldInit(pieces, req, cid);
requires call YieldBig(req, cid);

// requires {:layer 1} committed_requests == Set_Empty();
{
   var i: int;
   var j: Pid;
   var d: Decision;
   var v: Vote;
   var {:linear} pieces': Set ParticipantPiece;
   var {:linear} piece: One ParticipantPiece;
   pieces' := pieces;
   d := COMMIT();
   j := 1;
   while (j <= NumParticipants)
   invariant {:layer 1} 1 <= j && j <= NumParticipants + 1;
   invariant {:layer 1} pieces' == JParticipantPieces(req->val->id, j);
   {
    call piece := One_Get(pieces', (Fraction(req->val->id, j, ParticipantIds())));
    assert {:layer 1} participant_votes[piece->val->id][piece->val->val] == NULL();
    async call voting0(req->val, piece);
    j := j + 1;
   }
   i := 1;

   call YieldBig(req, cid);

   while (i <= NumParticipants)
   invariant {:layer 1} 1 <= i && i <= NumParticipants + 1;
   invariant {:layer 1} (d != ABORT()) ==> (forall k: Pid :: (1 <= k && k <= i-1)  ==> participant_votes[k][req->val->id] == YES());
   {
    call v := receive_vote(i, req->val->id);
    if (v == NO())
    {
    d := ABORT();
    // break;
    }
    i := i + 1;
   }

//    assume false;

   if (d == COMMIT()) {
        
        // assert {:layer 1} false;
     
        // locked requests of all pid have req
        // committed => locked
        // locked has no overlaps
        
        // all participants said yes
        assert {:layer 1} (forall p: Pid :: 1 <= p && p <= NumParticipants ==> participant_votes[p][req->val->id] == YES());
        
        // all participants have it locked
        assert {:layer 1} (forall pid : Pid :: 1 <= pid && pid <= NumParticipants ==> Set_Contains(locked_requests[pid], req->val));
        
        // locked requests of any pid never overlap
        assert {:layer 1} !(exists pid: Pid, req1: Request, req2: Request :: req1->id != req2->id && req1->duration == req2->duration && Set_Contains(locked_requests[pid], req1) && Set_Contains(locked_requests[pid], req2));
        
        // committed => locked
        assert {:layer 1} (forall req:Request ::  Set_Contains(committed_requests[cid->val], req)  ==> (forall pid: Pid :: (1 <= pid && pid <= NumParticipants) ==>  (Set_Contains(locked_requests[pid], req))));

        // assert {:layer 1} !(Set_Contains(committed_requests[cid->val], req->val));

        call add_to_committed_requests(cid, req);

        // assert {:layer 1} !(exists req': Request :: Set_Contains(committed_requests[cid->val], req') && req'->duration == req->val->duration);
    
        // assert {:layer 1} Set_Contains(committed_requests, req)  ==> (forall pid: Pid :: (1 <= pid && pid <= NumParticipants) ==>  (Set_Contains(locked_requests[pid], req)));
        // assert {:layer 1} !(exists req1: Request, req2: Request :: req1->id != req2->id && req1->duration == req2->duration && Set_Contains(committed_requests[cid->val], req1) && Set_Contains(committed_requests[cid->val], req2));

        // assert {:layer 1} !(exists req1: Request, req2: Request :: req1->id != req2->id && req1->duration == req2->duration && Set_Contains(committed_requests[cid->val], req1) && Set_Contains(committed_requests[cid->val], req2));
   }
}

async action {:layer 1} voting(req: Request, {:linear_in} piece: One ParticipantPiece) //(reqid, pid) (4, 3) (5, 3)
modifies locked_requests, participant_votes;
asserts IsValidParticipantPiece(piece->val) && piece->val->val == req->id;
asserts participant_votes[piece->val->id][piece->val->val] == NULL();
asserts !(Set_Contains(locked_requests[piece->val->id], req));
// asserts !(exists req0:Request :: Set_Contains(locked_requests[pid], req0) && req0->id == req->id);
// asserts participant_votes[pid][req] == NULL();
{
    
    // assert !(exists req0:Request :: Set_Contains(locked_requests[piece->val->id], req0) && req0->id == req->id);
    // assert participant_votes[piece->val->id][piece->val->val] == NULL();
    // if (*) {
    //     participant_votes[pid->val->id][req] := NO();
    //     return;
    // }
    // else {
        // assert participant_votes[piece->val->id][piece->val->val] == NULL();
        if (NoOverlap(locked_requests[piece->val->id], req)) {
            locked_requests[piece->val->id] := Set_Add(locked_requests[piece->val->id], req);
            participant_votes[piece->val->id][req->id] := YES();
        }
        else {
            participant_votes[piece->val->id][req->id] := NO();
        }
    // }
}
yield procedure {:layer 0} voting1(req: Request, {:linear_in} piece: One ParticipantPiece);
refines voting;

yield procedure {:layer 1} voting0(req: Request, {:linear_in}  piece: One ParticipantPiece)
// requires {:layer 1} IsValidParticipantPiece(piece->val) && piece->val->val == req->id;
requires call YieldVoting(piece, req);
// requires {:layer 1} participant_votes[piece->val->id][piece->val->val] == NULL();
// requires call YieldBig();
// requires call YieldVoting(piece);
{
    // assert {:layer 1} !(exists req0:Request :: Set_Contains((locked_requests)[pid], req0) && req0->id == req->id);
    // assert {:layer 1} participant_votes[piece->val->id][piece->val->val] == NULL();
    call voting1(req, piece);
}



action {:layer 1} ADD_TO_COMMITTED_REQUESTS({:linear_in} cid: One Cid, {:linear_in} req: One Request)
modifies committed_requests;
asserts (forall pid : Pid :: 1 <= pid && pid <= NumParticipants ==> Set_Contains(locked_requests[pid], req->val));
// asserts !(Set_Contains(committed_requests, req->val));
// asserts !(exists req0:Request :: Set_Contains(committed_requests, req0) && req0->id == req->id);
// asserts !(exists req1: Request :: req1->id != req->id && req1->duration == req->duration && Set_Contains(committed_requests, req1));
{
    committed_requests[cid->val] := Set_Add(committed_requests[cid->val], req->val);
}
yield procedure {:layer 0} add_to_committed_requests({:linear_in} cid: One Cid, {:linear_in} req: One Request);
refines ADD_TO_COMMITTED_REQUESTS;



right action {:layer 1} RECEIVE_VOTE(pid: Pid, reqId: ReqId) returns (v: Vote)
{
   assume participant_votes[pid][reqId] != NULL();
   v := participant_votes[pid][reqId];
}
yield procedure {:layer 0} receive_vote(pid: Pid,  reqId: ReqId) returns (v: Vote);
refines RECEIVE_VOTE;



action {:layer 1} WAIT_FOR_PARTICIPANT_VOTE(reqId: ReqId)
{
      assume (forall pid: Pid :: (1 <= pid && pid <= NumParticipants) ==> participant_votes[pid][reqId] != NULL());
}
yield procedure {:layer 0} wait_for_participant_vote(reqId: ReqId); 
refines WAIT_FOR_PARTICIPANT_VOTE;

