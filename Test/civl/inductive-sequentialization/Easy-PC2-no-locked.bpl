// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Pid = int;
type Duration = int;
type ReqId;

datatype Vote { YES(), NO(), NULL() }

datatype Decision { COMMIT(), ABORT(), NONE() }



datatype Request { Request(id: ReqId, duration: Duration )}

type ParticipantPiece = Fraction ReqId Pid;

const NumParticipants:int;
axiom NumParticipants > 0;
// axiom !(exists req1: Request, req2:Request :: req1->id == req2->id && req1->duration != req2->duration);


var {:layer 0,1} participant_votes: [Pid][Request]Vote;
var {:layer 0,1} committed_requests: (Set Request);

// yield invariant {:layer 1} YieldBig({:linear} req: One Request);
// invariant {:layer 1} (forall req:Request ::  Set_Contains(committed_requests, req)  ==> (forall pid: Pid :: Set_Contains(ParticipantIds(), pid) ==>  participant_votes[pid][req] == YES()));
// invariant !(Set_Contains(committed_requests, req->val));
// invariant !(exists req1: Request, req2: Request :: req1->id != req2->id && req1->duration == req2->duration && Set_Contains(committed_requests, req1) && Set_Contains(committed_requests, req2));

yield invariant {:layer 1} YieldParticipantVotes();
invariant !(exists pid: Pid, req1: Request, req2: Request :: Set_Contains(ParticipantIds(), pid) && req1->id != req2->id && req1->duration == req2->duration && participant_votes[pid][req1] == YES() && participant_votes[pid][req2] == YES() );

yield invariant {:layer 1} YieldVoting({:linear} piece: One ParticipantPiece, req: Request);
invariant IsValidParticipantPiece(piece->val) && piece->val->val == req->id;
invariant participant_votes[piece->val->id][req] == NULL();

yield invariant {:layer 1} YieldInit({:linear} pieces: Set ParticipantPiece, {:linear} req: One Request);
invariant pieces == AllParticipantPieces(req->val->id);
invariant (forall p: ParticipantPiece :: Set_Contains(pieces, p) ==> participant_votes[p->id][req->val] == NULL());
invariant !(Set_Contains(committed_requests, req->val));

// yield invariant {:layer 1} YieldCommittedReq({:linear} req: One Request);



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

yield invariant {:layer 1} YieldTrue();
invariant true;

yield procedure {:layer 1} coordinator({:linear_in} pieces: Set ParticipantPiece,  {:linear_in} req: One Request) // (1, 3) (1, 6) 
requires call YieldInit(pieces, req);
// requires call YieldBig(req);
// requires call YieldCommittedReq(req);
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
    assert {:layer 1} participant_votes[piece->val->id][req->val] == NULL();
    async call voting0(req->val, piece);
    j := j + 1;
   }
   i := 1;

//    call YieldBig(req);
   call YieldTrue();

   while (i <= NumParticipants)
   invariant {:layer 1} 1 <= i && i <= NumParticipants + 1;
   invariant {:layer 1} (d != ABORT()) ==> (forall k: Pid :: (1 <= k && k <= i-1)  ==> participant_votes[k][req->val] == YES());
   {
    call v := receive_vote(i, req->val);
    if (v == NO())
    {
    d := ABORT();
    // break;
    }
    i := i + 1;
   }


   if (d == COMMIT()) {
        
        // all participants said yes
        // assert {:layer 1} (forall p: Pid :: 1 <= p && p <= NumParticipants ==> participant_votes[p][req->val] == YES());
        // assert {:layer 1} !(exists pid: Pid, req1: Request, req2: Request :: 1 <= pid && pid <= NumParticipants  && req1->id != req2->id && req1->duration == req2->duration && participant_votes[pid][req1] == YES() && participant_votes[pid][req2] == YES() );
        // assert {:layer 1} (forall req:Request ::  Set_Contains(committed_requests, req)  ==> (forall pid: Pid :: (1 <= pid && pid <= NumParticipants) ==>  participant_votes[pid][req] == YES()));
        // assert {:layer 1} !(exists req1: Request, req2: Request :: req1->id != req2->id && req1->duration == req2->duration && Set_Contains(committed_requests, req1) && Set_Contains(committed_requests, req2));
        // assert {:layer 1} !Set_Contains(committed_requests, req->val);
        // assert {:layer 1} (forall req':Request :: Set_Contains(committed_requests, req') ==> req'->duration != req->val->duration);
        call add_to_committed_requests(req);
        }
}

async action {:layer 1} voting(req: Request, {:linear_in} piece: One ParticipantPiece) //(reqid, pid) (4, 3) (5, 3)
modifies participant_votes;
asserts IsValidParticipantPiece(piece->val) && piece->val->val == req->id;
asserts participant_votes[piece->val->id][req] == NULL();
{
        if ((forall req': Request :: participant_votes[piece->val->id][req'] == YES() ==> req'->duration != req->duration)) {
            participant_votes[piece->val->id][req] := YES();
        }
        else {
            participant_votes[piece->val->id][req] := NO();
        }
}
yield procedure {:layer 0} voting1(req: Request, {:linear_in} piece: One ParticipantPiece);
refines voting;

yield procedure {:layer 1} voting0(req: Request, {:linear_in}  piece: One ParticipantPiece)
requires call YieldVoting(piece, req);
{
    call voting1(req, piece);
}

action {:layer 1} ADD_TO_COMMITTED_REQUESTS({:linear_in} req: One Request)
modifies committed_requests;
// asserts (forall p: Pid :: 1 <= p && p <= NumParticipants ==> participant_votes[p][req->val] == YES());
// asserts !(Set_Contains(committed_requests, req->val));
// asserts  !(exists pid: Pid, req1: Request, req2: Request :: 1 <= pid && pid <= NumParticipants  && req1->id != req2->id && req1->duration == req2->duration && participant_votes[pid][req1] == YES() && participant_votes[pid][req2] == YES() );
// asserts !(exists req':Request :: req'->duration == req->val->duration && Set_Contains(committed_requests, req'));
{
    committed_requests := Set_Add(committed_requests, req->val);
}
yield procedure {:layer 0} add_to_committed_requests({:linear_in} req: One Request);
refines ADD_TO_COMMITTED_REQUESTS;

right action {:layer 1} RECEIVE_VOTE(pid: Pid, req: Request) returns (v: Vote)
{
   assume participant_votes[pid][req] != NULL();
   v := participant_votes[pid][req];
}
yield procedure {:layer 0} receive_vote(pid: Pid,  req: Request) returns (v: Vote);
refines RECEIVE_VOTE;

action {:layer 1} WAIT_FOR_PARTICIPANT_VOTE(req: Request)
{
      assume (forall pid: Pid :: (1 <= pid && pid <= NumParticipants) ==> participant_votes[pid][req] != NULL());
}
yield procedure {:layer 0} wait_for_participant_vote(req: Request); 
refines WAIT_FOR_PARTICIPANT_VOTE;

