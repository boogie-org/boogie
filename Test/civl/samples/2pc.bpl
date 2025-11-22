// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*
2pc protocol: 
A transaction needs to be executed at every replica. Every replica executes each step of the transaction
but does not mark the transaction as complete until the coordinator runs the 2pc protocol to collectively
decide whether to commit or abort the transaction.

There are two phases in the protocol. In the first phase, the coordinator sends vote requests to all replicas.
The replicas then send a reply (yes/no) to the coordinator. If all replies are yes, then the coordinator sends
a commit decision to all replicas, otherwise it sends an abort decision. After receiving the decision from the
coordinator, the transaction is marked as complete at each replica if it was a commit decision, or cancelled
if it was an abort decision.

Model proved below:
Let's say there are multiple transactions at each replica that are marked as incomplete. Then multiple instances
of the coordinator may be running concurrently, each executing the 2pc protocol one transaction.
The goal is to ensure that we don't ever commit conflicting transactions; this condition is used to
abstractly model consistency of committed transactions.
We model the conflict relation between transactions using a 2-d array Conflict with axioms.

Proof obligation:
We have a ghost variable, committed_transactions, which keeps track of all transactions that have been committed so far.
Before adding a transaction to this set, we assert that the transaction being added does not conflict with any previously
committed transactions. If this assertion is shown to hold in all executions of the protocol, it should imply that
we never commit conflicting transactions.
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

function noConflicts(xids: (Set TransactionId), xid: TransactionId) : bool
{
    !(exists x: TransactionId :: Set_Contains(xids, x) && Conflict[x][xid])
}

function {:inline} VoteRequests(xid: TransactionId, i: int, j: int) : Set (One VoteRequest)
{
    Set((lambda vr: One VoteRequest :: vr->val->xid == xid &&  i <= vr->val->rid && vr->val->rid <= j))
}

function allVoteRequests(xid: TransactionId) : Set (One VoteRequest)
{
    VoteRequests(xid, 1, n)
}

function remainingVoteRequests(xid: TransactionId, i: int) : Set (One VoteRequest)
{
    VoteRequests(xid, i, n)
}

yield procedure {:layer 1} TPC({:linear} xid: One TransactionId, {:linear_in} vrs: (Set (One VoteRequest)))
requires {:layer 1} vrs == allVoteRequests(xid->val);
requires call LockedNoConflicts();
requires call CommittedSubsetLocked();
requires call XidNotInCommitted(xid);
{
    var d: Decision;
    var votes: [ReplicaId]Vote;
    var {:linear} vrs': Set (One VoteRequest);
    var i: int;

    d := COMMIT();
    vrs' := vrs;

    call votes, vrs' := vote_all(xid->val, vrs', n);
    
    i := 1;
    while (i <= n)
    invariant {:layer 1} (forall {:pool "J"} j:int :: {:add_to_pool "J", j} 1 <= j && j < i ==> (d == COMMIT() ==> (votes[j] == YES())));
    {
        if (votes[i] == NO())
        {
            d := ABORT();
        }
        i := i+1;
    }

    call finalize_all(d, xid, vrs');

    if (d == COMMIT())
    {
        call LockedNoConflicts() | CommittedSubsetLocked() |  XidNotInCommitted(xid) | XidInLocked(xid);
        assume {:add_to_pool "J", 1} true;
        call add_to_committed_transactions(xid);
    }
}

yield right procedure {:layer 1} vote_all(xid: TransactionId, {:linear_in} vrs: Set (One VoteRequest), i: int) returns (votes: [ReplicaId]Vote, {:linear} vrs': Set (One VoteRequest))
requires {:layer 1} vrs == VoteRequests(xid, 1, i);
ensures {:layer 1} (forall j:int :: 1 <= j && j < i+1 && votes[j] == YES() ==> Set_Contains(locked_transactions[j], xid));
ensures {:layer 1} vrs' == VoteRequests(xid, 1, i);
preserves {:layer 1} LockedNoConflicts(locked_transactions);
preserves {:layer 1} CommittedSubsetLocked(locked_transactions, committed_transactions);
ensures {:layer 1} (forall j:int :: 1 <= j && j < n+1 ==> IsSubset(old(locked_transactions)[j]->val, locked_transactions[j]->val));
ensures {:layer 1} (forall j:int :: 1 <= j && j < i+1 ==> votes[j] != NONE());
modifies locked_transactions;
{
    var {:linear} vr: One VoteRequest;
    var out: Vote;

    vrs' := vrs;
    if (1 <= i)
    {
        vr := One(VoteRequest(xid, i));
        call One_Split(vrs', vr);
        call votes, vrs' := vote_all(xid, vrs', i-1) |  out := vote(vr);
        votes[i] := out;
        call One_Put(vrs', vr);
    }
}

yield left procedure {:layer 1} finalize_all(d: Decision, {:linear} xid: One TransactionId, {:linear_in} vrs: Set (One VoteRequest))
requires {:layer 1} vrs == allVoteRequests(xid->val);
requires {:layer 1}  (forall j:int :: {:add_to_pool "J", j} d == COMMIT() &&  1 <= j && j < n+1 ==> Set_Contains(locked_transactions[j], xid->val));
ensures {:layer 1}  (forall j:int :: d == COMMIT() && 1 <=j && j < n+1 ==> Set_Contains(locked_transactions[j], xid->val));
preserves {:layer 1} LockedNoConflicts(locked_transactions);
preserves {:layer 1} CommittedSubsetLocked(locked_transactions, committed_transactions);
requires {:layer 1} !Set_Contains(committed_transactions, xid->val);
ensures {:layer 1} (forall j:int, xid0 : TransactionId :: 1 <= j && j < n+1 && xid0 != xid->val && Set_Contains(old(locked_transactions)[j], xid0) ==> Set_Contains(locked_transactions[j], xid0));
modifies locked_transactions;
{
    var i: int;
    var {:linear} vr: One VoteRequest;
    var {:linear} vrs': Set (One VoteRequest);

    vrs' := vrs;
    i := 1;

    while (i <= n)
    invariant {:layer 1} (forall j:int :: d == COMMIT() && 1 <= j && j < i ==> Set_Contains(locked_transactions[j], xid->val));
    invariant {:layer 1} (forall j:int :: d == COMMIT() && (i <= j) && (j < n+1)  ==> Set_Contains(locked_transactions[j], xid->val));
    invariant {:layer 1} vrs' == remainingVoteRequests(xid->val, i);
    invariant {:layer 1} (forall  j:int,  xid1: TransactionId, xid2: TransactionId :: (1 <= j && j < n+1 && xid1 != xid2 && Set_Contains(locked_transactions[j], xid1) && Set_Contains(locked_transactions[j], xid2)) ==> !Conflict[xid1][xid2]);
    invariant {:layer 1} (forall j:int, xid0: TransactionId ::  1 <= j && j < n+1 && Set_Contains(committed_transactions, xid0) ==> Set_Contains(locked_transactions[j], xid0));
    invariant {:layer 1} !Set_Contains(committed_transactions, xid->val);
    invariant {:layer 1} (forall j:int, xid0 : TransactionId :: 1 <= j && j < n+1 && xid0 != xid->val && Set_Contains(old(locked_transactions)[j], xid0) ==> Set_Contains(locked_transactions[j], xid0));
    {
        vr := One(VoteRequest(xid->val, i));
        call One_Split(vrs', vr);
        async call {:sync} finalize(d, vr);
        i := i + 1;
    }
}

yield procedure {:layer 0} vote({:linear} vr: One VoteRequest) returns (result : Vote);
refines right action {:layer 1, 1} _ {
    if (*)
    {
        result := NO();
    }
    else
    {
        if (noConflicts(locked_transactions[vr->val->rid], vr->val->xid))
        {
            locked_transactions[vr->val->rid] := Set_Add(locked_transactions[vr->val->rid], vr->val->xid);
            result := YES();
        }
        else
        {
            result := NO();
        }
    }
}

yield procedure {:layer 0} finalize(d: Decision, {:linear} vr: One VoteRequest);
refines left action {:layer 1, 1} _ {
    if (d != COMMIT())
    {
        locked_transactions[vr->val->rid] := Set_Remove(locked_transactions[vr->val->rid], vr->val->xid);
    }
}

yield procedure {:layer 0} add_to_committed_transactions({:linear} xid: One TransactionId);
refines atomic action {:layer 1, 1} _ {
    assert (forall xid0: TransactionId :: Set_Contains(committed_transactions, xid0) ==> !Conflict[xid0][xid->val]);
    committed_transactions := Set_Add(committed_transactions, xid->val);
}

function {:inline} LockedNoConflicts(locked_transactions: [ReplicaId](Set TransactionId)) : bool
{
    (forall  {:pool "J"} j: int, xid1: TransactionId, xid2: TransactionId :: {:add_to_pool "J", j}
        1 <= j && j < n+1 && xid1 != xid2 && Set_Contains(locked_transactions[j], xid1) && Set_Contains(locked_transactions[j], xid2)
        ==> !Conflict[xid1][xid2])
}
yield invariant {:layer 1} LockedNoConflicts();
preserves {:layer 1} LockedNoConflicts(locked_transactions);

function {:inline} CommittedSubsetLocked(locked_transactions: [ReplicaId](Set TransactionId), committed_transactions: Set TransactionId) : bool
{
    (forall {:pool "J"} j: int, xid0: TransactionId :: {:add_to_pool "J", j}
        1 <= j && j < n+1 && Set_Contains(committed_transactions, xid0)
        ==> Set_Contains(locked_transactions[j], xid0))
}
yield invariant {:layer 1} CommittedSubsetLocked();
preserves {:layer 1} CommittedSubsetLocked(locked_transactions, committed_transactions);

yield invariant {:layer 1} XidInLocked({:linear} xid: One TransactionId);
preserves (forall {:pool "J"} j:int :: {:add_to_pool "J", j} 1 <= j && j < n+1 ==> Set_Contains(locked_transactions[j], xid->val));

yield invariant {:layer 1} XidNotInCommitted({:linear} xid: One TransactionId);
preserves !Set_Contains(committed_transactions, xid->val);
 
