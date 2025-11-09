// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*
This file contains a proof of the protocol from the following paper:

Hagit Attiya, Amotz Bar-Noy, and Danny Dolev.
Sharing Memory Robustly in Message-passing Systems.
J. ACM 42, 1 (1995), 124-142.

This protocol implements two operations Read and Write on a single register
that is replicated for fault-tolerance and shared across a collection of clients.
These operations are expected to provide a linearizable interface.

The Civl proof imposes the following abstraction on a detailed protocol specification.
This abstraction is proved linearizable informallyn but precisely towards
the end of this file.  

type TimeStamp  // a set with a total order
TS: TimeStamp   // global timestamp used to order operations
value_store: Map TimeStamp Value // store for timestamped values

// ReadClient is a wrapper procedure around the Read atomic operation.
// WriteClient is a wrapper procedure around the Write atomic operation.
// Begin and End are atomic operations used to mark the start and end of ReadClient and WriteClient.
// These markers are useful in specifying the linearizability of ReadClient and WriteClient.

ReadClient(one_pid) {
    old_ts := Begin(one_pid)
    <yield>
    ts, val := Read(one_pid, old_ts)
    <yield>
    End(one_pid, ts);
}

WriteClient(one_pid) {
    old_ts := Begin(one_pid)
    <yield>
    ts := Write(one_pid, old_ts)
    <yield>
    End(one_pid, ts);
}

Begin(one_pid) returns (ts) {
    ts = TS;
}

Read(one_pid, old_ts) returns (ts, val) {
    assume old_ts <= ts
    assume ts in value_store
    val := value_store[ts]
}

Write(one_pid, val) returns (ts) {
    assume old_ts < ts
    assume ts not in value_store
    value_store[ts] := val
}

End(one_pid, ts) {
    TS := max(TS, ts)
}
*/

//////////////////////////////////////////////////////////////////////////
// Types and Constants

const numReplicas: int; // number of replicas of the register
axiom numReplicas > 0;

type ReplicaId = int;
type ReplicaSet = [ReplicaId]bool;
type ProcessId = int;
type Value;

const InitValue: Value; // initial value of the register

datatype TimeStamp {
    TimeStamp(t: int, pid: ProcessId)
}

function {:inline} LeastTimeStamp(): TimeStamp { TimeStamp(0, 0) }

datatype StampedValue {
  StampedValue(ts: TimeStamp, value: Value)
}

//////////////////////////////////////////////////////////////////////////
// Functions and axiomns

function {:inline} NoReplicas(): ReplicaSet { MapConst(false) }
function {:inline} IsReplica(x: int): bool { 0 <= x && x < numReplicas }

function Cardinality(q: ReplicaSet): int;
axiom Cardinality(NoReplicas()) == 0;

function IsQuorum(rs: ReplicaSet): bool {
  2 * Cardinality(rs) > numReplicas &&
  (forall r: ReplicaId :: rs[r] ==> IsReplica(r))
}

axiom (forall rs1: ReplicaSet, rs2: ReplicaSet ::
  IsQuorum(rs1) && IsQuorum(rs2) ==> (exists r: ReplicaId :: IsReplica(r) && rs1[r] && rs2[r])
);

axiom (forall rs1: ReplicaSet, rs2: ReplicaSet :: IsQuorum(rs1) && IsSubset(rs1, rs2) ==> IsQuorum(rs2));

function {:inline} lt(ts1: TimeStamp, ts2: TimeStamp) : bool {
    (ts1->t < ts2->t) || (ts1->t == ts2->t && ts1->pid < ts2->pid)
}

function {:inline} le(ts1: TimeStamp, ts2: TimeStamp) : bool {
    ts1 == ts2 || lt(ts1, ts2)
}

//////////////////////////////////////////////////////////////////////////
// Global variables

var {:layer 1, 4} value_store: Map TimeStamp Value; // unified store of timestamped values shared across all replicas
var {:layer 1, 3} replica_ts: [ReplicaId]TimeStamp; // projection of replica_store to only the timestamps
var {:layer 1, 1} last_write: [ProcessId]int;   // last_write[pid] is the version number of the last write by process pid
var {:layer 0, 4} TS: TimeStamp;    // global timestamp used in the linearizability proof of the abstract protocol
var {:layer 0, 1} replica_store: [ReplicaId]StampedValue;   // state for concrete protocol

/*
The proof at layer 1 splits replica_store into replica_ts and value_store.

The proof at layer 2 abstracts Query and Begin operations so that Query becomes
a right mover and Update becomes a left mover. As a result, the bodies of Read
and Write become atomic blocks at layer 3.

The proof at layer 3 converts Read and Write into appropriate atomic actions to
enable the informal proof of linearizability of ReadClient and WriteClient.
*/

//////////////////////////////////////////////////////////////////////////
// Yield invariants

function {:inline} ValueStorePredicate(value_store: Map TimeStamp Value, ts: TimeStamp, value: Value) : bool
{
    Map_Contains(value_store, ts) && Map_At(value_store, ts) == value
}

yield invariant {:layer 1} Monotonic#1(cond: bool, ts: TimeStamp, rid: ReplicaId);
preserves cond ==> le(ts, replica_store[rid]->ts);

yield invariant {:layer 1} MonotonicInduction#1(q: ReplicaSet, ts: TimeStamp, i: int);
preserves (forall rid: ReplicaId:: q[rid] && i <= rid && rid < numReplicas ==> le(ts, replica_store[rid]->ts));

yield invariant {:layer 1} MonotonicAll(old_replica_store: [ReplicaId]StampedValue);
preserves (forall rid: ReplicaId:: IsReplica(rid) ==> le(old_replica_store[rid]->ts, replica_store[rid]->ts));

yield invariant {:layer 1} ReplicaInv();
preserves (forall rid: ReplicaId:: IsReplica(rid) ==>
            replica_ts[rid] == replica_store[rid]->ts
            && Map_Contains(value_store, replica_ts[rid])
            && Map_At(value_store, replica_ts[rid]) == replica_store[rid]->value);

yield invariant {:layer 1} LastWriteInv({:linear} one_pid: One ProcessId, pid_last_ts: TimeStamp);
preserves lt(TimeStamp(last_write[one_pid->val], one_pid->val), pid_last_ts);
preserves (forall ts: TimeStamp:: Map_Contains(value_store, ts) && ts->pid == one_pid->val ==> le(ts, pid_last_ts));

yield invariant {:layer 1} ValueStoreInv#1(ts: TimeStamp, value: Value);
preserves ValueStorePredicate(value_store, ts, value);

yield invariant {:layer 1} AddToValueStoreInv({:linear} one_pid: One ProcessId, ts: TimeStamp);
preserves one_pid->val == ts->pid;
preserves !Map_Contains(value_store, ts);

yield invariant {:layer 2} Monotonic#2(cond: bool, ts: TimeStamp, rid: ReplicaId);
preserves cond ==> le(ts, replica_ts[rid]);

yield invariant {:layer 2} MonotonicInduction#2(q: ReplicaSet, ts: TimeStamp, i: int);
preserves (forall rid: ReplicaId:: q[rid] && i <= rid && rid < numReplicas ==> le(ts, replica_ts[rid]));

yield invariant {:layer 2} TimeStampQuorum();
preserves (exists q: ReplicaSet:: IsQuorum(q) && (forall rid: ReplicaId:: q[rid] ==> le(TS, replica_ts[rid])));

yield invariant {:layer 2} ValidTimeStamp();
preserves (forall rid: ReplicaId :: le(LeastTimeStamp(), replica_ts[rid]));

yield invariant {:layer 3} ValueStoreInv#3(ts: TimeStamp, value: Value);
preserves ValueStorePredicate(value_store, ts, value);

yield invariant {:layer 4} Yield#4();

//////////////////////////////////////////////////////////////////////////
// Procedures and actions

yield procedure {:layer 4} ReadClient({:linear} one_pid: One ProcessId) returns (value: Value)
preserves call ValueStoreInv#1(LeastTimeStamp(), InitValue);
preserves call ReplicaInv();
preserves call ValidTimeStamp();
preserves call TimeStampQuorum();
preserves call ValueStoreInv#3(LeastTimeStamp(), InitValue);
{
    var old_ts: TimeStamp;
    var ts: TimeStamp;
    // tsq is the quorum witnessing the global timestamp TS
    var {:layer 2, 3} tsq: ReplicaSet;
    var {:layer 2} tsq': ReplicaSet;

    call old_ts, tsq := Begin(one_pid) | ValueStoreInv#1(LeastTimeStamp(), InitValue) | ValidTimeStamp() | ValueStoreInv#3(LeastTimeStamp(), InitValue);
    call Yield#4();
    call ts, value, tsq' := Read(one_pid, old_ts, tsq);
    call Yield#4();
    call End(one_pid, ts);
}

// lwq is the quorum witnessing the last write
yield procedure {:layer 4} WriteClient({:linear} one_pid: One ProcessId, value: Value, {:hide} {:layer 1} lwq: ReplicaSet)
    returns (ts: TimeStamp, {:hide} {:layer 1} lwq': ReplicaSet)
requires call MonotonicInduction#1(lwq, TimeStamp(last_write[one_pid->val], one_pid->val), 0);
ensures call MonotonicInduction#1(lwq', ts, 0);
requires call LastWriteInv(one_pid, TimeStamp(last_write[one_pid->val], one_pid->val));
ensures call LastWriteInv(one_pid, ts);
preserves call ValidTimeStamp();
preserves call TimeStampQuorum();
preserves call ValueStoreInv#3(LeastTimeStamp(), InitValue);
{
    var old_ts: TimeStamp;
    // tsq is the quorum witnessing the global timestamp TS
    var {:layer 2, 3} tsq: ReplicaSet;
    var {:layer 2} tsq': ReplicaSet;

    call old_ts, tsq := Begin(one_pid) | ValidTimeStamp() | ValueStoreInv#3(LeastTimeStamp(), InitValue);
    call Yield#4();
    call ts, lwq', tsq' := Write(one_pid, value, old_ts, lwq, tsq);
    call Yield#4();
    call End(one_pid, ts);
}

yield procedure {:layer 3} Begin({:linear} one_pid: One ProcessId) returns (ts: TimeStamp, {:hide} {:layer 2, 3} tsq: ReplicaSet)
refines action {:layer 4} _ {
    ts := TS;
}
preserves call ReplicaInv();
preserves call ValidTimeStamp();
ensures call MonotonicInduction#2(tsq, ts, 0);
preserves call TimeStampQuorum();
ensures {:layer 3} IsQuorum(tsq);
{
    call ts, tsq := Begin#2(one_pid);
}

yield procedure {:layer 3} Read({:linear} one_pid: One ProcessId, old_ts: TimeStamp, {:hide} {:layer 2, 3} tsq: ReplicaSet)
    returns (ts: TimeStamp, value: Value, {:hide} {:layer 2} tsq': ReplicaSet)
refines action {:layer 4} _ { 
    assume le(old_ts, ts);
    assume Map_Contains(value_store, ts);
    value := Map_At(value_store, ts);
}
preserves call ValueStoreInv#1(LeastTimeStamp(), InitValue);
preserves call ReplicaInv();
preserves call MonotonicInduction#2(tsq, old_ts, 0);
preserves call ValidTimeStamp();
preserves call TimeStampQuorum();
ensures call MonotonicInduction#2(tsq', ts, 0);
ensures {:layer 2} IsQuorum(tsq');
requires {:layer 3} IsQuorum(tsq);
preserves call ValueStoreInv#3(LeastTimeStamp(), InitValue);
{
    var {:layer 1} old_replica_store: [ReplicaId]StampedValue;

    call {:layer 1} old_replica_store := Copy(replica_store);
    call ts, value, tsq' := QueryPhase(old_ts, old_replica_store, tsq);
    call tsq' := UpdatePhase(ts, value) | MonotonicInduction#2(tsq, old_ts, 0) | ValidTimeStamp() | ValueStoreInv#1(LeastTimeStamp(), InitValue);
}

yield procedure {:layer 3}
Write({:linear} one_pid: One ProcessId, value: Value, old_ts: TimeStamp, {:hide} {:layer 1} lwq: ReplicaSet, {:hide} {:layer 2, 3} tsq: ReplicaSet)
    returns (ts: TimeStamp, {:hide} {:layer 1} lwq': ReplicaSet, {:hide} {:layer 2} tsq': ReplicaSet)
refines action {:layer 4} _ {
    assume lt(old_ts, ts);
    assume !Map_Contains(value_store, ts);
    value_store := Map_Update(value_store, ts, value);
}
requires call MonotonicInduction#1(lwq, TimeStamp(last_write[one_pid->val], one_pid->val), 0);
ensures call MonotonicInduction#1(lwq', ts, 0);
requires call LastWriteInv(one_pid, TimeStamp(last_write[one_pid->val], one_pid->val));
ensures call LastWriteInv(one_pid, ts);
preserves call MonotonicInduction#2(tsq, old_ts, 0);
preserves call ValidTimeStamp();
preserves call TimeStampQuorum();
ensures call MonotonicInduction#2(tsq', ts, 0);
ensures {:layer 2} IsQuorum(tsq');
requires {:layer 3} IsQuorum(tsq);
preserves call ValueStoreInv#3(LeastTimeStamp(), InitValue);
{
    var q: ReplicaSet;
    var _value: Value;
    var {:layer 1} old_replica_store: [ReplicaId]StampedValue;

    call {:layer 1} old_replica_store := Copy(replica_store);
    call ts, _value, q := QueryPhase(old_ts, old_replica_store, tsq) | LastWriteInv(one_pid, TimeStamp(last_write[one_pid->val], one_pid->val));
    ts := TimeStamp(ts->t + 1, one_pid->val);
    call AddToValueStore(one_pid, ts, value);
    call q := UpdatePhase(ts, value) | LastWriteInv(one_pid, ts) | MonotonicInduction#2(tsq, old_ts, 0) | ValidTimeStamp();
    lwq' := q;
    tsq' := q;
}

yield right procedure {:layer 3} QueryPhase(old_ts: TimeStamp, {:layer 1} old_replica_store: [ReplicaId]StampedValue, {:layer 2, 3} tsq: ReplicaSet)
    returns (max_ts: TimeStamp, max_value: Value, q: ReplicaSet)
preserves call ValueStoreInv#1(LeastTimeStamp(), InitValue);
preserves call ReplicaInv();
preserves call MonotonicAll(old_replica_store);
ensures call ValueStoreInv#1(max_ts, max_value);
ensures {:layer 1} IsQuorum(q) && (forall rid: ReplicaId:: q[rid] ==> le(old_replica_store[rid]->ts, max_ts));
preserves call MonotonicInduction#2(tsq, old_ts, 0);
preserves call ValidTimeStamp();
preserves call TimeStampQuorum();
requires {:layer 3} IsQuorum(tsq);
preserves {:layer 3} ValueStorePredicate(value_store, LeastTimeStamp(), InitValue);
ensures {:layer 3} le(old_ts, max_ts);
ensures {:layer 3} Map_Contains(value_store, max_ts) && Map_At(value_store, max_ts) == max_value;
{
    assume IsQuorum(q);
    call max_ts, max_value := QueryPhaseHelper(0, q, old_ts, old_replica_store, tsq);
}

yield right procedure {:layer 3}
QueryPhaseHelper(i: int, q: ReplicaSet, old_ts: TimeStamp, {:layer 1} old_replica_store: [ReplicaId]StampedValue, {:layer 2, 3} tsq: ReplicaSet)
    returns (max_ts: TimeStamp, max_value: Value)
requires {:layer 1, 2} IsReplica(i) || i == numReplicas;
preserves call ValueStoreInv#1(LeastTimeStamp(), InitValue);
preserves call ReplicaInv();
preserves call MonotonicAll(old_replica_store);
ensures call ValueStoreInv#1(max_ts, max_value);
ensures {:layer 1} (forall rid: ReplicaId:: q[rid] && i <= rid && rid < numReplicas ==> le(old_replica_store[rid]->ts, max_ts));
preserves call MonotonicInduction#2(tsq, old_ts, 0);
preserves call ValidTimeStamp();
preserves call TimeStampQuorum();
preserves {:layer 3} ValueStorePredicate(value_store, LeastTimeStamp(), InitValue);
ensures {:layer 3} (exists rid: ReplicaId:: i <= rid && rid < numReplicas && q[rid] && tsq[rid]) ==> le(old_ts, max_ts);
ensures {:layer 3} Map_Contains(value_store, max_ts) && Map_At(value_store, max_ts) == max_value;
{
    var ts: TimeStamp;
    var value: Value;

    if (i == numReplicas)
    {
        max_ts := LeastTimeStamp();
        max_value := InitValue;
        return;
    }
    call ts, value := Query#2(i, q, old_replica_store[i]->ts, old_ts, tsq) | 
        max_ts, max_value := QueryPhaseHelper(i + 1, q, old_ts, old_replica_store, tsq);
    if (lt(max_ts, ts))
    {
        max_ts := ts;
        max_value := value;
    }
}

yield left procedure {:layer 3} UpdatePhase(ts: TimeStamp, value: Value) returns (q: ReplicaSet)
preserves call ReplicaInv();
preserves call ValueStoreInv#1(ts, value);
ensures call MonotonicInduction#1(q, ts, 0);
preserves call TimeStampQuorum();
ensures call MonotonicInduction#2(q, ts, 0);
ensures {:layer 2} IsQuorum(q);
{
    assume IsQuorum(q);
    call UpdatePhaseHelper(0, ts, value, q);
}

yield left procedure {:layer 3} UpdatePhaseHelper(i: int, ts: TimeStamp, value: Value, q: ReplicaSet)
requires {:layer 1} IsReplica(i) || i == numReplicas;
requires {:layer 1} IsQuorum(q);
preserves call ReplicaInv();
preserves call ValueStoreInv#1(ts, value);
ensures call MonotonicInduction#1(q, ts, i);
preserves call TimeStampQuorum();
ensures call MonotonicInduction#2(q, ts, i);
{
    if (i == numReplicas)
    {
        return;
    }
    call Update#2(i, ts, value, q) | UpdatePhaseHelper(i + 1, ts, value, q);
}

yield procedure {:layer 2} Begin#2({:linear} one_pid: One ProcessId) returns (ts: TimeStamp, {:layer 2} tsq: ReplicaSet)
refines action {:layer 3} _ {
    ts := TS;
    assume IsQuorum(tsq) && (forall rid: ReplicaId :: tsq[rid] ==> le(ts, replica_ts[rid]));
}
preserves call ReplicaInv();
preserves call ValidTimeStamp();
ensures call MonotonicInduction#2(tsq, ts, 0);
preserves call TimeStampQuorum();
{
    call ts := Begin#0(one_pid);
    call {:layer 2} tsq := CalculateQuorum(replica_ts, ts);
    assert {:layer 2} (exists q: ReplicaSet:: IsQuorum(q) && IsSubset(q, tsq));
}

pure procedure {:inline 1} CalculateQuorum(replica_ts: [ReplicaId]TimeStamp, ts: TimeStamp) returns (w: ReplicaSet)
{
    // calculate the set of all replica ids whose timestamp is at least ts
    w := (lambda rid: ReplicaId:: IsReplica(rid) && le(ts, replica_ts[rid]));
}

yield procedure {:layer 2} Query#2(rid: ReplicaId, q: ReplicaSet, {:hide} {:layer 1} old_replica_ts: TimeStamp, old_ts: TimeStamp, {:layer 2} tsq: ReplicaSet)
    returns (ts: TimeStamp, value: Value)
refines right action {:layer 3} _ {
    if (q[rid])
    {
        if (tsq[rid])
        {
            assume le(old_ts, ts) && le(ts, replica_ts[rid]);
        }
        else
        {
            assume le(LeastTimeStamp(), ts) && le(ts, replica_ts[rid]);
        }
        assume Map_Contains(value_store, ts);
        value := Map_At(value_store, ts);
    }
    else
    {
        ts := LeastTimeStamp();
        value := InitValue;
    }
}
requires call ValueStoreInv#1(LeastTimeStamp(), InitValue);
requires {:layer 1, 2} IsReplica(rid);
requires call Monotonic#1(true, old_replica_ts, rid);
preserves call ReplicaInv();
ensures call ValueStoreInv#1(ts, value);
ensures {:layer 1} q[rid] ==> le(old_replica_ts, ts);
preserves call MonotonicInduction#2(tsq, old_ts, 0);
preserves call ValidTimeStamp();
preserves call TimeStampQuorum();
{
    if (q[rid])
    {
        call ts, value := Query#1(rid, old_replica_ts);
    }
    else
    {
        ts := LeastTimeStamp();
        value := InitValue;
    }
}

yield procedure {:layer 2} Update#2(rid: ReplicaId, ts: TimeStamp, value: Value, q: ReplicaSet)
refines left action {:layer 3} _ {
    if (q[rid])
    {
        if (lt(replica_ts[rid], ts)) {
            replica_ts[rid] := ts;
        }
    }
}
requires {:layer 1} IsReplica(rid);
preserves call ReplicaInv();
preserves call ValueStoreInv#1(ts, value);
ensures call Monotonic#1(q[rid], ts, rid);
ensures call Monotonic#2(q[rid], ts, rid);
preserves call TimeStampQuorum();
{
    if (q[rid])
    {
        call Update#1(rid, ts, value);
    }
}

yield procedure {:layer 1} Query#1(rid: ReplicaId, {:hide} {:layer 1} old_replica_ts: TimeStamp) returns (ts: TimeStamp, value: Value)
refines action {:layer 2} _ {
    ts := replica_ts[rid];
    assume Map_Contains(value_store, ts);
    value := Map_At(value_store, ts);
}
requires {:layer 1} IsReplica(rid);
preserves call ReplicaInv();
requires call Monotonic#1(true, old_replica_ts, rid);
ensures {:layer 1} le(old_replica_ts, ts);
ensures call ValueStoreInv#1(ts, value);
{
    call ts, value := Query#0(rid);
}

yield procedure {:layer 1} AddToValueStore({:linear} one_pid: One ProcessId, ts: TimeStamp, value: Value)
refines action {:layer 2, 3} _ {
    assume !Map_Contains(value_store, ts);
    value_store := Map_Update(value_store, ts, value);
}
requires call AddToValueStoreInv(one_pid, ts);
requires call LastWriteInv(one_pid, TimeStamp(last_write[one_pid->val], one_pid->val));
ensures call LastWriteInv(one_pid, ts);
{
    call {:layer 1} last_write := Copy(last_write[ts->pid := ts->t]);
    call {:layer 1} value_store := Copy(Map_Update(value_store, ts, value));
}

yield procedure {:layer 1} Update#1(rid: ReplicaId, ts: TimeStamp, value: Value)
refines action {:layer 2} _ {
    if (lt(replica_ts[rid], ts)) {
        replica_ts[rid] := ts;
    }
}
requires {:layer 1} IsReplica(rid);
preserves call ReplicaInv();
preserves call ValueStoreInv#1(ts, value);
ensures call Monotonic#1(true, ts, rid);
{
    call Update#0(rid, ts, value);
    call {:layer 1} replica_ts := Copy(replica_ts[rid := replica_store[rid]->ts]);
}

yield procedure {:layer 0} Begin#0({:linear} one_pid: One ProcessId) returns (ts: TimeStamp);
refines action {:layer 1, 2} _ {
    ts := TS;
}

yield procedure {:layer 0} Query#0(rid: ReplicaId) returns (ts: TimeStamp, value: Value);
refines action {:layer 1} _ {
    var sv: StampedValue;

    sv := replica_store[rid];
    StampedValue(ts, value) := sv;
}

yield procedure {:layer 0} Update#0(rid: ReplicaId, ts: TimeStamp, value: Value);
refines action {:layer 1} _ {
    var sv: StampedValue;

    sv := replica_store[rid];
    if (lt(sv->ts, ts)) {
        replica_store[rid] := StampedValue(ts, value);
    }
}

yield procedure {:layer 0} End({:linear} one_pid: One ProcessId, ts: TimeStamp);
refines action {:layer 1, 4} _ {
    if (lt(TS, ts)) {
        TS := ts;
    }
}

/*
We prove that the last layer shown below is linearizable.

// Definition of <HB
Given any concurrent execution, we define a happens-before order (<HB) as follows:
op1 <HB op2 iff End of op1 executes before Begin of op2. We have the following two lemmas about <HB.

// HB_Lemma 1: <HB is a strict partial order
The proof follows from the totally-ordered nature of a concurrent execution.

// HB_Lemma 2: if op1 <HB op2, then op1.ts <= op2.ts
  Case 1: op2 is a write
          From the specification "assume old_ts < ts" for writes, we have op1.ts < op2.ts
  Case 2: op2 is a read
          From the specification "assume old_ts <= ts" for reads, we have op1.ts <= op2.ts

// Definition of <L
Given any concurrent execution, we construct a linearization order (<L) of ReadClient and WriteClient operations
that is a correct sequential specification of an atomic register and is consistent with <HB.
We associate WriteClient and ReadClient with the ts that is calculated in their Write and Read actions, respectively.
From this point on, we'll refer to WriteClient and ReadClient operations simply as write and read,
and write.ts and read.ts to refer to their associated timestamp.

Order op1 <L op2: 
C1. if op1.ts < op2.ts, or
C2. if op1.ts == op2.ts and op1 is a write and op2 is a read, or
C3. if op1.ts == op2.ts and both are reads and op1 <HB op2 

// <L is a strict partial order
Irreflexive: not(op <L op)
op.ts < op.ts is not possible
op can't be both a read and a write 
op <HB op is not possible (since <HB is a strict partial order)

Asymmetry: if op1 <L op2,  then not(op2 <L op1)
Case 1: op1.ts < op2.ts => not(op2.ts < op1.ts) and not(op2.ts == op1.ts), therefore we have not(op2 <L op1)
Case 2: op1.ts == op2.ts
        Case 2.1: op1 is a write and op2 is a read
                  therefore we have not(op2 <L op1)
        Case 2.2: op1 is a read and op2 is a read
                  since op1 <L op2, we must have op1 <HB op2, which implies not(op2 <HB op1) (since <HB is a strict partial order)
                  therefore we have not(op2 <L op1)

Transitivity: if op1 <L op2 and op2 <L op3,  then op1 <L op3
op1.ts <= op2.ts and op2.ts <= op3.ts ==> op1.ts <= op3.ts (transitive property of inequality)
Case 1: op1.ts < op3.ts then op1 <L op3 (from C1)
Case 2: op1.ts == op3.ts
          op1.ts == op3.ts implies op1.ts == op2.ts == op3.ts 
          Case 2.1: op1 is a write and op2 is a read and op3 is a read
                    op1.ts == op3.ts and op1 is a write and op3 is a read ==> op1 <L op3 (from C2)
          Case 2.2: op1 is a read and op2 is a read and op3 is a read
                    we have op1 <HB op2 <HB op3 => op1 <HB op3 (<HB is a strict partial order)
                    since op1.ts == op3.ts and op1 <HB < op3, we have op1 <L op3 (from C3)                

// Show that the reads return values consistent with an atomic register
We prove that in <L every read returns the value written by the last preceding write. 
From the specification "assume ts is not in value_store" for writes, we get that for any two write operations w1 and w2,
either w1.ts < w2.ts or w2.ts < w1.ts holds. 
This implies w1 <L w2 or w2 <L w1 (from C1)
From the specification "assume ts in value_store" for reads, we get that any read r reads something that is written by some write w.
Therefore, w.ts == r.ts, which implies w <L r (from C2)
From the above two points, we can conclude that there exists a subset of <L that forms a total order over all writes and any given read r, as follows: 
w_0 < ... < w_i < r < w_(i+1) < ... < w_n, where w_i.ts == r.ts
Since any total order of <L will respect this order among writes and a read, we can conclude that the read returns the value written by the last preceding write.

// Show that <L is consistent with happens before order: op1 <HB op2 ==> op1 <L op2
we have op1.ts <= op2.ts (from HB_Lemma 2)
Case 1: op1.ts < op2.ts, then we have op1 <L op2 (from C1)
Case 2: op1.ts == op2.ts
     Case 2.1: op1 is a read and op2 is a write
               But from the specification "assume old_ts < ts" for writes, we must have op1.ts < op2.ts. Therefore, this case is not possible.
     Case 2.2: op1 is a read and op2 is  aread
               and we also have op1 <HB op2, which implies op1 <L op2 (from C3)
     Case 2.3: op1 is a write and op2 is a read
               we have op1 <L op2 (from C2)
Therefore, any total ordering of <L will also be consistent with <HB.
*/