//////////////////////////////////////////////////////////////////////////
// Types and Constants
const numReplicas: int;
axiom numReplicas > 0;

type ReplicaId = int;
type ProcessId = int;
type Value;

const InitValue: Value;

type ReplicaSet = [ReplicaId]bool;
function {:inline} IsReplica(x: int): bool { 0 <= x && x < numReplicas }

datatype TimeStamp {
    TimeStamp(t: int, pid: ProcessId)
}

function {:inline} LeastTimeStamp(): TimeStamp { TimeStamp(0, 0) }

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
  (forall r: ReplicaId :: rs[r] ==> IsReplica(r))
}

axiom (forall rs1: ReplicaSet, rs2: ReplicaSet ::
  IsQuorum(rs1) && IsQuorum(rs2) ==> (exists r: ReplicaId :: IsReplica(r) && rs1[r] && rs2[r])
);

function {:inline} lt(ts1: TimeStamp, ts2: TimeStamp) : bool {
    (ts1->t < ts2->t) || (ts1->t == ts2->t && ts1->pid < ts2->pid)
}

function {:inline} le(ts1: TimeStamp, ts2: TimeStamp) : bool {
    ts1 == ts2 || lt(ts1, ts2)
}

//////////////////////////////////////////////////////////////////////////
// Global variables

var {:layer 1, 4} value_store: Map TimeStamp Value;
var {:layer 1, 3} replica_ts: [ReplicaId]TimeStamp;
var {:layer 1, 1} last_write: [ProcessId]int;
var {:layer 0, 4} TS: TimeStamp;
var {:layer 0, 1} replica_store: [ReplicaId]StampedValue;

//////////////////////////////////////////////////////////////////////////
// Yield invariants

yield invariant {:layer 1} Monotonic(cond: bool, ts: TimeStamp, rid: ReplicaId);
invariant cond ==> le(ts, replica_store[rid]->ts);

yield invariant {:layer 1} MonotonicAll(old_replica_store: [ReplicaId]StampedValue);
invariant (forall rid: ReplicaId:: IsReplica(rid) ==> le(old_replica_store[rid]->ts, replica_store[rid]->ts));

yield invariant {:layer 1} MonotonicInduction(q: ReplicaSet, ts: TimeStamp, i: int);
invariant (forall rid: ReplicaId:: q[rid] && i <= rid && rid < numReplicas ==> le(ts, replica_store[rid]->ts));

yield invariant {:layer 1} ReplicaInv();
invariant (forall rid: ReplicaId:: IsReplica(rid) ==>
            replica_ts[rid] == replica_store[rid]->ts
            && Map_Contains(value_store, replica_ts[rid])
            && Map_At(value_store, replica_ts[rid]) == replica_store[rid]->value);

yield invariant {:layer 1} LastWriteInv({:linear} one_pid: One ProcessId, pid_last_ts: TimeStamp);
invariant lt(TimeStamp(last_write[one_pid->val], one_pid->val), pid_last_ts);
invariant (forall ts: TimeStamp:: Map_Contains(value_store, ts) && ts->pid == one_pid->val ==> le(ts, pid_last_ts));

yield invariant {:layer 1} ValueStoreInv(ts: TimeStamp, value: Value);
invariant Map_Contains(value_store, ts) && Map_At(value_store, ts) == value;

yield invariant {:layer 1} AddToValueStoreInv({:linear} one_pid: One ProcessId, ts: TimeStamp);
invariant one_pid->val == ts->pid;
invariant !Map_Contains(value_store, ts);

yield invariant {:layer 4} Yield#4();

//////////////////////////////////////////////////////////////////////////
// Procedures and actions

yield procedure {:layer 4} ReadClient({:linear} one_pid: One ProcessId) returns (value: Value)
requires call ValueStoreInv(LeastTimeStamp(), InitValue);
preserves call ReplicaInv();
{
    var old_ts: TimeStamp;
    var {:layer 2, 3} w: ReplicaSet;
    var ts: TimeStamp;

    par old_ts, w := Begin(one_pid) | ValueStoreInv(LeastTimeStamp(), InitValue);
    call Yield#4();
    call ts, value := Read(one_pid, old_ts, w);
    call Yield#4();
    call End(one_pid, ts);
}

yield procedure {:layer 4} WriteClient({:linear} one_pid: One ProcessId, value: Value, in: ReplicaSet) returns (ts: TimeStamp, out: ReplicaSet)
requires call MonotonicInduction(in, TimeStamp(last_write[one_pid->val], one_pid->val), 0);
ensures call MonotonicInduction(out, ts, 0);
requires call LastWriteInv(one_pid, TimeStamp(last_write[one_pid->val], one_pid->val));
ensures call LastWriteInv(one_pid, ts);
{
    var old_ts: TimeStamp;
    var {:layer 2, 3} w: ReplicaSet;

    call old_ts, w := Begin(one_pid);
    call Yield#4();
    call out, ts := Write(one_pid, value, in, old_ts, w);
    call Yield#4();
    call End(one_pid, ts);
}

yield procedure {:layer 3} Begin({:linear} one_pid: One ProcessId) returns (ts: TimeStamp, {:hide} {:layer 2, 3} w: ReplicaSet)
refines action {:layer 4} _ {
    ts := TS;
}
preserves call ReplicaInv();
{
    call ts, w := Begin#2(one_pid);
}

yield procedure {:layer 3} Read({:linear} one_pid: One ProcessId, old_ts: TimeStamp, {:hide} {:layer 2, 3} w: ReplicaSet) returns (ts: TimeStamp, value: Value)
refines action {:layer 4} _ { 
    assume le(old_ts, ts);
    assume Map_Contains(value_store, ts);
    value := Map_At(value_store, ts);
}
requires call ValueStoreInv(LeastTimeStamp(), InitValue);
preserves call ReplicaInv();
{
    var q: ReplicaSet;
    var {:layer 1} old_replica_store: [ReplicaId]StampedValue;

    call {:layer 1} old_replica_store := Copy(replica_store);
    call ts, value, q := QueryPhase(old_replica_store, old_ts, w);
    call q := UpdatePhase(ts, value);
}

yield procedure {:layer 3} Write({:linear} one_pid: One ProcessId, value: Value, in: ReplicaSet, old_ts: TimeStamp, {:hide} {:layer 2, 3} w: ReplicaSet) returns ( out: ReplicaSet, ts: TimeStamp)
refines action {:layer 4} _ {
    assume lt(old_ts, ts);
    assume !Map_Contains(value_store, ts);
    value_store := Map_Update(value_store, ts, value);
}
requires call MonotonicInduction(in, TimeStamp(last_write[one_pid->val], one_pid->val), 0);
ensures call MonotonicInduction(out, ts, 0);
requires call LastWriteInv(one_pid, TimeStamp(last_write[one_pid->val], one_pid->val));
ensures call LastWriteInv(one_pid, ts);
{
    var q: ReplicaSet;
    var _value: Value;
    var {:layer 1} old_replica_store: [ReplicaId]StampedValue;

    call {:layer 1} old_replica_store := Copy(replica_store);
    par ts, _value, q := QueryPhase(old_replica_store, old_ts, w) | LastWriteInv(one_pid, TimeStamp(last_write[one_pid->val], one_pid->val));
    ts := TimeStamp(ts->t + 1, one_pid->val);
    call AddToValueStore(one_pid, ts, value);
    par out := UpdatePhase(ts, value) | LastWriteInv(one_pid, ts);
}

yield right procedure {:layer 3} QueryPhase({:layer 1} old_replica_store: [ReplicaId]StampedValue, old_ts: TimeStamp, {:layer 2, 3} w: ReplicaSet) returns (max_ts: TimeStamp, max_value: Value, q: ReplicaSet)
requires call ValueStoreInv(LeastTimeStamp(), InitValue);
preserves call ReplicaInv();
preserves call MonotonicAll(old_replica_store);
ensures call ValueStoreInv(max_ts, max_value);
ensures {:layer 1} IsQuorum(q) && (forall rid: ReplicaId:: q[rid] ==> le(old_replica_store[rid]->ts, max_ts));
{
    assume IsQuorum(q);
    call max_ts, max_value := QueryPhaseHelper(0, q, old_replica_store, old_ts, w);
}

yield right procedure {:layer 3} QueryPhaseHelper(i: int, q: ReplicaSet, {:layer 1} old_replica_store: [ReplicaId]StampedValue, old_ts: TimeStamp, {:layer 2, 3} w: ReplicaSet) returns (max_ts: TimeStamp, max_value: Value)
requires {:layer 1} IsReplica(i) || i == numReplicas;
preserves call ValueStoreInv(LeastTimeStamp(), InitValue);
preserves call ReplicaInv();
preserves call MonotonicAll(old_replica_store);
ensures call ValueStoreInv(max_ts, max_value);
ensures {:layer 1} (forall rid: ReplicaId:: q[rid] && i <= rid && rid < numReplicas ==> le(old_replica_store[rid]->ts, max_ts));
{
    var ts: TimeStamp;
    var value: Value;

    if (i == numReplicas)
    {
        max_ts := LeastTimeStamp();
        max_value := InitValue;
        return;
    }
    par ts, value := Query#2(i, q, old_replica_store[i]->ts, old_ts, w) | 
        max_ts, max_value := QueryPhaseHelper(i + 1, q, old_replica_store, old_ts, w);
    if (lt(max_ts, ts))
    {
        max_ts := ts;
        max_value := value;
    }
}

yield left procedure {:layer 3} UpdatePhase(ts: TimeStamp, value: Value) returns (q: ReplicaSet)
preserves call ReplicaInv();
preserves call ValueStoreInv(ts, value);
ensures call MonotonicInduction(q, ts, 0);
{
    assume IsQuorum(q);
    call UpdatePhaseHelper(0, ts, value, q);
}

yield left procedure {:layer 3} UpdatePhaseHelper(i: int, ts: TimeStamp, value: Value, q: ReplicaSet)
requires {:layer 1} IsReplica(i) || i == numReplicas;
requires {:layer 1} IsQuorum(q);
preserves call ReplicaInv();
preserves call ValueStoreInv(ts, value);
ensures call MonotonicInduction(q, ts, i);
{
    if (i == numReplicas)
    {
        return;
    }
    par Update#2(i, ts, value, q) | UpdatePhaseHelper(i + 1, ts, value, q);
}

yield procedure {:layer 2} Begin#2({:linear} one_pid: One ProcessId) returns (ts: TimeStamp, {:layer 2} w: ReplicaSet)
refines action {:layer 3} _ {
    ts := TS;
    assume (forall rid: ReplicaId :: w[rid] ==> le(ts, replica_ts[rid]));
}
preserves call ReplicaInv();
{
    call ts := Begin#0(one_pid);
    call {:layer 2} w := CalculateQuorum(replica_ts, ts);
}

pure procedure {:inline 1} CalculateQuorum(replica_ts: [ReplicaId]TimeStamp, ts: TimeStamp) returns (w: ReplicaSet)
{
    // calculate the set of all replica ids whose timestamp is at least ts
    w := (lambda rid: ReplicaId:: IsReplica(rid) && le(ts, replica_ts[rid]));
}

yield procedure {:layer 2} Query#2(rid: ReplicaId, q: ReplicaSet, {:hide} {:layer 1} old_replica_ts: TimeStamp, old_ts: TimeStamp, {:layer 2} w: ReplicaSet) returns (ts: TimeStamp, value: Value)
refines right action {:layer 3} _ {
    if (q[rid])
    {
        if (w[rid])
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
requires call ValueStoreInv(LeastTimeStamp(), InitValue);
requires {:layer 1} IsReplica(rid);
requires call Monotonic(true, old_replica_ts, rid);
preserves call ReplicaInv();
ensures call ValueStoreInv(ts, value);
ensures {:layer 1} q[rid] ==> le(old_replica_ts, ts);
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
preserves call ValueStoreInv(ts, value);
ensures call Monotonic(q[rid], ts, rid);
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
requires call Monotonic(true, old_replica_ts, rid);
ensures {:layer 1} le(old_replica_ts, ts);
ensures call ValueStoreInv(ts, value);
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
preserves call ValueStoreInv(ts, value);
ensures call Monotonic(true, ts, rid);
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
