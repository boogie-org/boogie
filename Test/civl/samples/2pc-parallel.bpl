// Running the file:  boogie 2pc-parallel.bpl /keepQuantifier

/*
2pc protocol: 
A transaction needs to be executed at every replica. Every replica executes each step of the transaction but does not mark the transaction as complete until the coordinator runs the 2pc protocol to collectively decide whether to commit or abort the transaction. There are two phases in the protocol. In the first phase, the coordinator sends vote requests to all replicas. The replicas then send a reply (yes/no) to the coordinator. If all replies are yes, then the coordinator sends a commit decision to all replicas, otherwise it sends an abort decision. After receiving the decision from the coordinator, the transaction is marked as complete at each replica if it was a commit decision, or cancelled if it was an abort decision.

Model proved below:
Let's say there are multiple transactions at each replica that are marked as incomplete. It is now the coordinator's job to start the 2pc protocol for all of these transactions, and it does so concurrently. The goal is that we don't ever commit conflicting transactions because we can't control the order in which these transactions are applied at each replica. If conflicting transactions are committed, the data may no longer be same across all replicas.

Proof obligation: We have a ghost variable, committed_transactions, which keeps track of all transactions that have been committed so far. Before adding a transaction to this set, we assert that the transaction being added does not conflict with any previously committed transactions. If this assertion is shown to hold in all executions of the protocol, it should imply that we never commit conflicting transactions.
*/



type TransactionId;
type ReplicaId = int;

datatype Vote { YES(), NO(), NONE() }
datatype VoteRequest { VoteRequest(xid: TransactionId, rid: ReplicaId) }
datatype VoteRequestToken { VoteRequestToken(xid: TransactionId, rid: ReplicaId) }
datatype Decision { COMMIT(), ABORT() }

const Conflict: [TransactionId][TransactionId]bool;
const n: int;
axiom 0 < n;
axiom (forall xid1: TransactionId, xid2: TransactionId :: Conflict[xid1][xid2] == Conflict[xid2][xid1]);
axiom (forall xid0: TransactionId :: Conflict[xid0][xid0] == true);

var {:layer 0,1} locked_transactions: [ReplicaId](Set TransactionId);
var {:layer 0,1} committed_transactions: Set TransactionId;

function noConflicts(xids: (Set TransactionId), xid: TransactionId) : bool {
    !(exists x: TransactionId :: Set_Contains(xids, x) && Conflict[x][xid])
}

function allVoteRequests(xid: TransactionId) : Set VoteRequest {
    Set((lambda vr:VoteRequest :: vr->xid == xid &&  1 <= vr->rid && vr->rid < n+1))
}

function remainingVoteRequests(xid: TransactionId, i:int) : Set VoteRequest {
    Set((lambda vr:VoteRequest :: vr->xid == xid &&  i <= vr->rid && vr->rid < n+1))
}

right action {:layer 1, 1} voting_action ( {:linear} vr: One VoteRequest) returns (result : Vote)
{
    if(*) {
        result := NO();
    }
    else {
        if(noConflicts(locked_transactions[vr->val->rid], vr->val->xid)) {
            locked_transactions[vr->val->rid] := Set_Add(locked_transactions[vr->val->rid], vr->val->xid);
            result := YES();
        }
        else {
            result := NO();
        }
    }
}

yield procedure {:layer 0} voting_procedure ({:linear} vr: One VoteRequest) returns (result : Vote);
refines voting_action;

yield right procedure {:layer 1} voting_loop_yield_procedure(xid: TransactionId, {:linear_in} vrs: Set VoteRequest, i: int) returns (votes: [ReplicaId]Vote, {:linear} vrs': Set VoteRequest)
requires {:layer 1} vrs == Set((lambda vr:VoteRequest :: vr->xid == xid && 1 <= vr->rid && vr->rid < i+1));
ensures {:layer 1} (forall j:int :: 1 <= j && j < i+1 && votes[j] == YES() ==> Set_Contains(locked_transactions[j], xid));
ensures {:layer 1} vrs' ==Set((lambda vr:VoteRequest :: vr->xid == xid && 1 <= vr->rid && vr->rid < i+1));
preserves call LockedNoConflicts();
preserves call CommittedSubsetLocked();
ensures {:layer 1} (forall j:int :: 1 <= j && j < n+1 ==> IsSubset(old(locked_transactions)[j]->val, locked_transactions[j]->val));
ensures {:layer 1} (forall j:int :: 1 <= j && j < i+1 ==> votes[j] != NONE());
modifies locked_transactions;
{
    // var i: int;
    var {:linear} vr: One VoteRequest;
    var out: Vote;
    vrs' := vrs;
    // i := 1;
    // while( i<=n )
    // invariant {:layer 1} (forall j:int :: 1 <= j && j < i && replica_votes[VoteRequest(xid, j)] == YES() ==> Set_Contains(locked_transactions[j], xid));
    // invariant {:layer 1} IsSubset(remainingVoteRequests(xid, i)->val, vrs'->val);
    // invariant {:layer 1} vrs' == allVoteRequests(xid);
    // invariant {:layer 1} (forall  j:int,  xid1: TransactionId, xid2: TransactionId :: (1 <= j && j < n+1 && xid1 != xid2 && Set_Contains(locked_transactions[j], xid1) && Set_Contains(locked_transactions[j], xid2)) ==> !Conflict[xid1][xid2]);
    // invariant {:layer 1} (forall j:int, xid0: TransactionId ::  1 <= j && j < n+1 && Set_Contains(committed_transactions, xid0) ==> Set_Contains(locked_transactions[j], xid0));
    // invariant {:layer 1} (forall j:int :: 1 <=j && j < n+1 ==> IsSubset(old(locked_transactions)[j]->val, locked_transactions[j]->val));
    // invariant {:layer 1} (forall j:int :: 1 <= j && j < i ==> replica_votes[VoteRequest(xid, j)] != NONE());
    // {
        // call vr := One_Get(vrs', VoteRequest(xid, i));
        // call voting_procedure(vr);
        // i := i + 1;
        // call One_Put(vrs', vr);

        if(1 <= i)
        {
            call vr := One_Get(vrs', VoteRequest(xid, i));
            par votes, vrs' := voting_loop_yield_procedure(xid, vrs', i-1) |  out := voting_procedure(vr);
            votes[i] := out;
            call One_Put(vrs', vr);
        }
    // }
}

left action {:layer 1, 1} finalize_action (d: Decision, {:linear} vr: One VoteRequest)
{
   if(d == COMMIT())
    {

    }
    else
    {
        locked_transactions[vr->val->rid] := Set_Remove(locked_transactions[vr->val->rid], vr->val->xid);
    }
}


yield procedure {:layer 0} finalize_procedure (d: Decision, {:linear} vr: One VoteRequest);
refines finalize_action;

yield left procedure {:layer 1} finalize_loop_yield_procedure(d: Decision, {:linear} xid: One TransactionId, {:linear_in} vrs: Set VoteRequest)
requires {:layer 1} vrs == allVoteRequests(xid->val);
requires {:layer 1}  (forall j:int :: d == COMMIT() &&  1 <= j && j < n+1 ==> Set_Contains(locked_transactions[j], xid->val));
ensures {:layer 1}  (forall j:int :: d == COMMIT() && 1 <=j && j < n+1 ==> Set_Contains(locked_transactions[j], xid->val));
preserves call LockedNoConflicts();
preserves call CommittedSubsetLocked();
requires {:layer 1} !Set_Contains(committed_transactions, xid->val);
ensures {:layer 1} (forall j:int, xid0 : TransactionId :: 1 <= j && j < n+1 && xid0 != xid->val && Set_Contains(old(locked_transactions)[j], xid0) ==> Set_Contains(locked_transactions[j], xid0));
modifies locked_transactions;
{
    var i: int;
    var {:linear} vr: One VoteRequest;
    var {:linear} vrs': Set VoteRequest;
    vrs' := vrs;
    i := 1;

    while(i <= n)
    invariant {:layer 1} (forall j:int :: d == COMMIT() && 1 <= j && j < i ==> Set_Contains(locked_transactions[j], xid->val));
    invariant {:layer 1} (forall j:int :: d == COMMIT() && (i <= j) && (j < n+1)  ==> Set_Contains(locked_transactions[j], xid->val));
    invariant {:layer 1} vrs' == remainingVoteRequests(xid->val, i);
    invariant {:layer 1} (forall  j:int,  xid1: TransactionId, xid2: TransactionId :: (1 <= j && j < n+1 && xid1 != xid2 && Set_Contains(locked_transactions[j], xid1) && Set_Contains(locked_transactions[j], xid2)) ==> !Conflict[xid1][xid2]);
    invariant {:layer 1} (forall j:int, xid0: TransactionId ::  1 <= j && j < n+1 && Set_Contains(committed_transactions, xid0) ==> Set_Contains(locked_transactions[j], xid0));
    invariant {:layer 1} !Set_Contains(committed_transactions, xid->val);
    invariant {:layer 1} (forall j:int, xid0 : TransactionId :: 1 <= j && j < n+1 && xid0 != xid->val && Set_Contains(old(locked_transactions)[j], xid0) ==> Set_Contains(locked_transactions[j], xid0));
    {
        call vr := One_Get(vrs', VoteRequest(xid->val, i));
        async call {:sync} finalize_procedure(d, vr);
        i := i + 1;
    }
}

atomic action {:layer 1, 1} add_to_committed_transactions({:linear} xid: One TransactionId){
    assert (forall xid0: TransactionId :: Set_Contains(committed_transactions, xid0) ==> !Conflict[xid0][xid->val]);
    committed_transactions := Set_Add(committed_transactions, xid->val);
}

yield procedure {:layer 0} add_to_committed_transactions_procedure ({:linear} xid: One TransactionId);
refines add_to_committed_transactions;


yield procedure {:layer 1} TPC({:linear} xid: One TransactionId, {:linear_in} vrs: (Set VoteRequest))
requires {:layer 1} vrs == allVoteRequests(xid->val);
requires call LockedNoConflicts();
requires call CommittedSubsetLocked();
requires call XidNotInCommitted(xid);
{
    var d: Decision;
    var votes: [ReplicaId]Vote;
    var {:linear} vrs': Set VoteRequest;
    var i: int;
    d := COMMIT();
    vrs' := vrs;

    call votes, vrs' := voting_loop_yield_procedure(xid->val, vrs', n);
    
    i := 1;
    while(i <= n)
    invariant {:layer 1} (forall j:int :: 1 <= j && j < i ==> (d == COMMIT() ==> (votes[j] == YES())));
    {
        if(votes[i] == NO())
        {
            d := ABORT();
        }
        i := i+1;
    }

    call finalize_loop_yield_procedure(d, xid, vrs');

    if (d == COMMIT())
    {
        par LockedNoConflicts() | CommittedSubsetLocked() |  XidNotInCommitted(xid) | XidInLocked(xid);

        assume {:add_to_pool "J", 1} true;

        call add_to_committed_transactions_procedure(xid);
    }
}

yield invariant {:layer 1} LockedNoConflicts();
invariant {:layer 1} (forall  {:pool "J"} j:int, xid1: TransactionId, xid2: TransactionId :: (1 <= j && j < n+1 && xid1 != xid2 && Set_Contains(locked_transactions[j], xid1) && Set_Contains(locked_transactions[j], xid2)) ==> !Conflict[xid1][xid2]);

yield invariant {:layer 1} CommittedSubsetLocked();
invariant {:layer 1} (forall {:pool "J"} j:int, xid0: TransactionId ::  1 <= j && j < n+1 && Set_Contains(committed_transactions, xid0) ==> Set_Contains(locked_transactions[j], xid0));

yield invariant {:layer 1} XidInLocked({:linear} xid: One TransactionId);
invariant (forall {:pool "J"} j:int ::1 <=j && j < n+1 ==> Set_Contains(locked_transactions[j], xid->val));

yield invariant {:layer 1} XidNotInCommitted({:linear} xid: One TransactionId);
invariant !Set_Contains(committed_transactions, xid->val);
 
