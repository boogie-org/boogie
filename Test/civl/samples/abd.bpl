// ########## Last layer specification ##########

// type TimeStamp  // a set with a total order
// TS: TimeStamp   // global timestamp used to order operations
// store: Map TimeStamp Value // store for values

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

// Begin(one_pid) returns (ts)
//     ts = TS;

// Read(one_pid, old_ts) returns (ts, val)
//     assume old_ts <= ts
//     assume ts in store
//     val := store[ts]

// Write(one_pid, val) returns (ts)
//     assume old_ts < ts
//     assume ts not in store
//     store[ts] := val

// End(one_pid, ts)
//     TS := max(TS, ts) 


// ############## Why is this linearizable? #################

// Given any concurrent execution, we define a happens-before order (<HB) as follows: op1 <HB op2 iff End of op1 executes before Begin of op2. We have the following two lemmas about <HB.

// ############  HB_Lemma 1: <HB is a strict partial order ###############
// The proof follows from the totally-ordered nature of a concurrent execution.

// ############  HB_Lemma 2: if op1 <HB op2, then op1.ts <= op2.ts #############
//
//   Case 1: op2 is a write
//           From the specification "assume old_ts < ts" for writes, we have op1.ts < op2.ts
//   Case 2: op2 is a read
//           From the specification "assume old_ts <= ts" for reads, we have op1.ts <= op2.ts


// Given any concurrent execution, we construct a linearization order (<L) of ReadClient and WriteClient operations that is a correct sequential specification of an atomic register and is consistent with <HB.

// We associate WriteClient and ReadClient with the ts that is calculated in their Write and Read actions, respectively. From this point on, we'll refer to WriteClient and ReadClient operations simply as write and read, and write.ts and read.ts to refer to their associated timestamp.

// Order op1 <L op2: 
// C1. if op1.ts < op2.ts, or
// C2. if op1.ts == op2.ts and op1 is a write and op2 is a read, or
// C3. if op1.ts == op2.ts and both are reads and op1 <HB op2 

// ############# <L is a strict partial order ###############

// Irreflexive: not(op <L op)
// op.ts < op.ts is not possible
// op can't be both a read and a write 
// op <HB op is not possible (since <HB is a strict partial order)

// Asymmetry: if op1 <L op2,  then not(op2 <L op1)
// Case 1: op1.ts < op2.ts => not(op2.ts < op1.ts) and not(op2.ts == op1.ts), therefore we have not(op2 <L op1)
// Case 2: op1.ts == op2.ts
//         Case 2.1: op1 is a write and op2 is a read
//                   therefore we have not(op2 <L op1)
//         Case 2.2: op1 is a read and op2 is a read
//                   since op1 <L op2, we must have op1 <HB op2, which implies not(op2 <HB op1) (since <HB is a strict partial order)
//                   therefore we have not(op2 <L op1)

// Transitivity: if op1 <L op2 and op2 <L op3,  then op1 <L op3
// op1.ts <= op2.ts and op2.ts <= op3.ts ==> op1.ts <= op3.ts (transitive property of inequality)
// Case 1: op1.ts < op3.ts then op1 <L op3 (from C1)
// Case 2: op1.ts == op3.ts
//           op1.ts == op3.ts implies op1.ts == op2.ts == op3.ts 
//           Case 2.1: op1 is a write and op2 is a read and op3 is a read
//                     op1.ts == op3.ts and op1 is a write and op3 is a read ==> op1 <L op3 (from C2)
//           Case 2.2: op1 is a read and op2 is a read and op3 is a read
//                     we have op1 <HB op2 <HB op3 => op1 <HB op3 (<HB is a strict partial order)
//                     since op1.ts == op3.ts and op1 <HB < op3, we have op1 <L op3 (from C3)                

// ########## Show that the reads return values consistent with an atomic register: in <L every read returns the value written by the last preceding write. ###############

// From the specification "assume ts is not in store" for writes, we get that for any two write operations w1 and w2, either w1.ts < w2.ts or w2.ts < w1.ts holds. 
// This implies w1 <L w2 or w2 <L w1 (from C1)

// From the specification "assume ts in store" for reads, we get that any read r reads something that is written by some write w. Therefore, w.ts == r.ts, which implies w <L r (from C2)

// From the above two points, we can conclude that there exists a subset of <L that forms a total order over all writes and any given read r, as follows: 
// w_0 < ... < w_i < r < w_(i+1) < ... < w_n, where w_i.ts == r.ts

// Since any total order of <L will respect this order among writes and a read, we can conclude that the read returns the value written by the last preceding write.

// ########## Show that <L is consistent with happens before order: op1 <HB op2 ==> op1 <L op2 #############

// we have op1.ts <= op2.ts (from HB_Lemma 2)

// Case 1: op1.ts < op2.ts, then we have op1 <L op2 (from C1)
// Case 2: op1.ts == op2.ts
//      Case 2.1: op1 is a read and op2 is a write
//                But from the specification "assume old_ts < ts" for writes, we must have op1.ts < op2.ts. Therefore, this case is not possible.
//      Case 2.2: op1 is a read and op2 is  aread
//                and we also have op1 <HB op2, which implies op1 <L op2 (from C3)
//      Case 2.3: op1 is a write and op2 is a read
//                we have op1 <L op2 (from C2)

// Therefore, any total ordering of <L will also be consistent with <HB.

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


