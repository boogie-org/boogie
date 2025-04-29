// ########## Last layer specification ##########

// type TimeStamp  // a set with a total order
// TS: TimeStamp   // global timestamp used to order operations
// store: Map TimeStamp Value // store for values

// Client(one_pid){
//     var v;
//     if(*){
//         ReadClient(one_pid)
//     }
//     else{
//         WriteClient(one_pid, v)
//     }
// }

// ReadClient(one_pid){
//         old_ts := Begin(one_pid)
//         <yield>
//         ts, val := Read(one_pid, old_ts)
//         <yield>
//         End(one_pid, ts);
// }

// WriteClient(one_pid){
//         old_ts := Begin(one_pid)
//         <yield>
//         ts := Write(one_pid, old_ts)
//         <yield>
//         End(one_pid, ts);
// }

// Begin(one_pid) returns old_ts
//     ts = TS;

// Read(one_pid, old_ts) returns (ts, val)
//     var ts
//     assume old_ts <= ts
//     assume ts in store
//     val := store[ts]

// Write(one_pid, val)
//     var ts
//     assume old_ts < ts
//     assume ts not in store
//     store[ts] := val

// End(pid) returns (one_pid, ts)
//     var ts
//     TS := max(TS, ts) 


// ############## Why is this linearizable? #################

// Given any concurrent execution, we construct a linearization order (<L) of ReadClient and WriteClient operations that is a correct sequential specification of an atomic register and is consistent with the happens before order (<HB).

// We associate WriteClient and ReadClient with the ts that is calculated in their Write and Read actions respectively. From now on, I use write and read to refer to WriteClient and ReadClient operations,  and write.ts and read.ts to refer to their associated timestamp.

// Order op1 <L op2: 
// 1. if op1.ts < op2.ts, or
// 2. if op1.ts == op2.ts and op1 is a write and op2 is a read, or
// 3. if op1.ts == op2.ts and both are reads and op1 <HB op2, or 
// 4. if op1.ts == op2.ts and both are reads and both are parallel (not related by HB) and we feel like putting op1 before op2.

// ########## Show that <L is a total order ##################

// From the specification proved ("assume ts not in store" in Write) all the writes have strictly increasing ts, and from the specification proved ("assume ts in store" in Read) every read reads a value written by some write.
// Intuitively: We place all writes in their ts order, and every read will be placed between the writes w1 and w2, such that w1.ts == read.ts and read.ts < w2.ts. Among the reads in between two writes, we choose some extension of the <HB partial order.

// ########## Show that the reads return values consistent with an atomic register: in <L every read returns the value written by the last preceding write. ###############

// From the specification proved (assume ts in store) we get that the read reads something that is written.
// In the <L order it is clear that the read is placed in between the writes w1 and w2, such that w1.ts == read.ts and read.ts < w2.ts, 

// ########## Show that <L is consistent with happens before order: op1 <HB op2 ==> op1 <L op2 #############s

// Case1: op1 is read and op2 is write
// From the specification proved we have op1.ts < op2.ts, so op1 <L op2
// Case2: op1 is read and op2 is read
// From the specification proved we have op1.ts <= op2.ts
//     Case 2.1: if op1.ts < op2.ts, then we have op1 <L op2
//     Case 2.2: if op1.ts == op2.ts, then we order according to HB so we also have op1 <L op2.
// Case3: op1 is write and op2 is read
// From the specification proved we have op1.ts <= op2.ts
//     Case 3.1: if op1.ts < op2.ts then we have op1 <L op2
//     Case 3.2: if op1.ts == op2.ts then we place read after write so we have op1 <L op2
// Case4: op1 is write and op2 is write 
// From the specification proved we have op1.ts < op2.ts, so op1 <L op2


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


