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

The Civl proof imposes an abstraction on a detailed protocol specification
in which the actions READCLIENT and WRITECLIENT represent the atomic operations
on the register.
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

var {:layer 1, 5} value_store: Map TimeStamp Value; // unified store of timestamped values shared across all replicas
var {:layer 1, 3} replica_ts: [ReplicaId]TimeStamp; // projection of replica_store to only the timestamps
var {:layer 1, 1} last_write: [ProcessId]int;   // last_write[pid] is the version number of the last write by process pid
var {:layer 0, 5} TS: TimeStamp;    // global timestamp used in the linearizability proof of the abstract protocol
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
refines READCLIENT;
{
    var old_ts: TimeStamp;
    var ts: TimeStamp;
    // tsq is the quorum witnessing the global timestamp TS
    var {:layer 2, 3} tsq: ReplicaSet;
    var {:layer 2} tsq': ReplicaSet;

    call old_ts, tsq := Begin(one_pid) | ValueStoreInv#1(LeastTimeStamp(), InitValue) | ValidTimeStamp() | ValueStoreInv#3(LeastTimeStamp(), InitValue);
    call ts, value, tsq' := Read(one_pid, old_ts, tsq);
    call End(one_pid, ts);
}

action {:layer 5} READCLIENT({:linear} one_pid: One ProcessId) returns (value: Value)
{
    var old_ts: TimeStamp;
    var ts: TimeStamp;
    // tsq is the quorum witnessing the global timestamp TS
    var {:layer 2, 3} tsq: ReplicaSet;
    var {:layer 2} tsq': ReplicaSet;

    call old_ts := BEGIN#4(one_pid);
    call ts, value := READ#4(one_pid, old_ts);
    call End#4(one_pid, ts);
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
refines WRITECLIENT;
{
    var old_ts: TimeStamp;
    // tsq is the quorum witnessing the global timestamp TS
    var {:layer 2, 3} tsq: ReplicaSet;
    var {:layer 2} tsq': ReplicaSet;

    call old_ts, tsq := Begin(one_pid) | ValidTimeStamp() | ValueStoreInv#3(LeastTimeStamp(), InitValue);
    call ts, lwq', tsq' := Write(one_pid, value, old_ts, lwq, tsq);
    call End(one_pid, ts);
}

action {:layer 5} WRITECLIENT({:linear} one_pid: One ProcessId, value: Value)
    returns (ts: TimeStamp)
{
    var old_ts: TimeStamp;
    // tsq is the quorum witnessing the global timestamp TS
    var {:layer 2, 3} tsq: ReplicaSet;
    var {:layer 2} tsq': ReplicaSet;

    call old_ts := BEGIN#4(one_pid);
    call ts := WRITE#4(one_pid, value, old_ts);
    call End#4(one_pid, ts);
}

yield procedure {:layer 3} Begin({:linear} one_pid: One ProcessId) returns (ts: TimeStamp, {:hide} {:layer 2, 3} tsq: ReplicaSet)
refines BEGIN#4;
preserves call ReplicaInv();
preserves call ValidTimeStamp();
ensures call MonotonicInduction#2(tsq, ts, 0);
preserves call TimeStampQuorum();
ensures {:layer 3} IsQuorum(tsq);
{
    call ts, tsq := Begin#2(one_pid);
}

right action {:layer 4,5} BEGIN#4({:linear} one_pid: One ProcessId) returns (ts: TimeStamp) {
    assume le(ts, TS);
}

yield procedure {:layer 3} Read({:linear} one_pid: One ProcessId, old_ts: TimeStamp, {:hide} {:layer 2, 3} tsq: ReplicaSet)
    returns (ts: TimeStamp, value: Value, {:hide} {:layer 2} tsq': ReplicaSet)
refines READ#4;
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

right action {:layer 4,5} READ#4({:linear} one_pid: One ProcessId, old_ts: TimeStamp)
    returns (ts: TimeStamp, value: Value)
{
    assume le(old_ts, ts);
    assume Map_Contains(value_store, ts);
    value := Map_At(value_store, ts);
}

yield procedure {:layer 3}
Write({:linear} one_pid: One ProcessId, value: Value, old_ts: TimeStamp, {:hide} {:layer 1} lwq: ReplicaSet, {:hide} {:layer 2, 3} tsq: ReplicaSet)
    returns (ts: TimeStamp, {:hide} {:layer 1} lwq': ReplicaSet, {:hide} {:layer 2} tsq': ReplicaSet)
refines WRITE#4;
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

action {:layer 4,5} WRITE#4({:linear} one_pid: One ProcessId, value: Value, old_ts: TimeStamp)
    returns (ts: TimeStamp)
{
    assume lt(old_ts, ts);
    assume !Map_Contains(value_store, ts);
    value_store := Map_Update(value_store, ts, value);
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

pure action CalculateQuorum(replica_ts: [ReplicaId]TimeStamp, ts: TimeStamp) returns (w: ReplicaSet)
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
refines End#3;

action {:layer 1, 3} End#3({:linear} one_pid: One ProcessId, ts: TimeStamp)
refines End#4;
{
    if (lt(TS, ts)) {
        TS := ts;
    }
}

left action {:layer 4,5} End#4({:linear} one_pid: One ProcessId, ts: TimeStamp) {
    if (lt(TS, ts)) {
        TS := ts;
    }
}

