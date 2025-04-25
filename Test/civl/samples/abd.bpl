//////////////////////////////////////////////////////////////////////////
// Types and Constants
const numReplicas: int;
axiom numReplicas > 0;

type ReplicaId = int;
type ProcessId = int;
type Value;

type ReplicaSet = [ReplicaId]bool;
function Replica(x: int): bool { 1 <= x && x <= numReplicas }

datatype TimeStamp {
    TimeStamp(t: int, pid: ProcessId)
}

datatype StampedValue {
  StampedValue(ts: TimeStamp, value: Value)
}

//////////////////////////////////////////////////////////////////////////
// Functions
function {:inline} NoReplicas(): ReplicaSet { MapConst(false) }

function Cardinality(q: ReplicaSet): int;
axiom Cardinality(NoReplicas()) == 0;

function IsQuorum(rs: ReplicaSet): bool {
  2 * Cardinality(rs) > numReplicas &&
  (forall r: ReplicaId :: rs[r] ==> Replica(r))
}

axiom (forall rs1: ReplicaSet, rs2: ReplicaSet ::
  IsQuorum(rs1) && IsQuorum(rs2) ==> (exists r: ReplicaId :: Replica(r) && rs1[r] && rs2[r])
);

function greaterOrEqual(ts1: TimeStamp, ts2: TimeStamp) : bool{
    (ts1->t > ts2->t) || (ts1->t == ts2->t && ts1->pid > ts2->pid) || (ts1->t == ts2->t && ts1->pid == ts2->pid)
}

function greater(ts1: TimeStamp, ts2: TimeStamp) : bool{
    (ts1->t > ts2->t) || (ts1->t == ts2->t && ts1->pid > ts2->pid)
}

function maxSv(svs: Set StampedValue): StampedValue;
axiom (forall svs: Set StampedValue :: Set_Contains(svs, maxSv(svs)));
axiom (forall svs: Set StampedValue, sv: StampedValue :: Set_Contains(svs, sv) ==> greaterOrEqual(maxSv(svs)->ts, sv->ts));

//////////////////////////////////////////////////////////////////////////
// Global variables
var {:layer 0, 1} replica_store: [ReplicaId]StampedValue;

//////////////////////////////////////////////////////////////////////////
// Yield invariants
yield invariant {:layer 1} YieldTrue();

//////////////////////////////////////////////////////////////////////////
// Procedures and actions

yield procedure {:layer 1} Read({:linear} pid: One ProcessId) returns (val: Value)
{
    var query_quorum: ReplicaSet;
    var update_quorum: ReplicaSet;
    var replies: Set StampedValue;
    var max_sv: StampedValue;

    assume IsQuorum(query_quorum);
    call replies := QueryPhase(query_quorum);

    max_sv := maxSv(replies);

    assume IsQuorum(update_quorum);
    call UpdatePhase(update_quorum, max_sv);

    val := max_sv->value;
}

yield procedure {:layer 1} Write({:linear} pid: One ProcessId, val: Value)
{
    var query_quorum: ReplicaSet;
    var update_quorum: ReplicaSet;
    var replies: Set StampedValue;
    var max_sv: StampedValue;
    var new_sv: StampedValue;

    assume IsQuorum(query_quorum);
    call replies := QueryPhase(query_quorum);

    max_sv := maxSv(replies);
    new_sv := StampedValue(TimeStamp(max_sv->ts->t + 1, pid->val), val);

    assume IsQuorum(update_quorum);
    call UpdatePhase(update_quorum, new_sv);
}

// Parallel attempt not working
// yield procedure {:layer 1} QueryPhase(q: ReplicaSet, i: ReplicaId) returns (replies: Set StampedValue)
// {
//     var out: StampedValue;
//     var rid: ReplicaId;
//     if (i==0) {
//         return;
//     }
//     if (q[i]) {
//         par replies := QueryPhase(q, i-1) | out := Query0(i) | YieldTrue();
//     }
//     else {
//         call replies := QueryPhase(q, i-1);
//     }
//     replies := Set_Add(replies, out);
// }

yield procedure {:layer 1} QueryPhase(q: ReplicaSet) returns (replies: Set StampedValue)
{
    var out: StampedValue;
    var i: int;
    i := 0;

    while (i < numReplicas)
    invariant {:yields} {:layer 1} true;
    {
        if(q[i]){
            call out := Query0(i);
            replies := Set_Add(replies, out);
        }
    }
}

yield procedure {:layer 1} UpdatePhase(q: ReplicaSet, sv': StampedValue)
{
    var i: int;
    i := 0;

    while (i < numReplicas)
    invariant {:yields} {:layer 1} true;
    {
        if(q[i]){
            call Update0(i, sv');
        }
    }
}

yield procedure {:layer 0} Query0(rid: ReplicaId) returns (out: StampedValue);
refines Query;

action {:layer 1} Query(rid: ReplicaId) returns (out: StampedValue)
{
    out := replica_store[rid];
}

yield procedure {:layer 0} Update0(rid: ReplicaId, sv': StampedValue);
refines Update;

action {:layer 1} Update(rid: ReplicaId, sv': StampedValue){
    var sv: StampedValue;
    sv := replica_store[rid];
    if (greater(sv'->ts, sv->ts)){
        replica_store[rid] := sv';
    }
}


