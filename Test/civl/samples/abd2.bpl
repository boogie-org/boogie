//////////////////////////////////////////////////////////////////////////
// Types and Constants
const numReplicas: int;
axiom numReplicas > 0;

type ReplicaId = int;
type ProcessId = int;
type Value;

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

yield invariant {:layer 4} Yield();

//////////////////////////////////////////////////////////////////////////
// Procedures and actions

yield procedure {:layer 4} ReadClient({:linear} pid: One ProcessId) returns (value: Value)
{
    var old_ts: TimeStamp;
    var {:layer 2, 4} w: ReplicaSet;
    var ts: TimeStamp;

    call old_ts, w := Begin(pid);
    call Yield();
    call ts, value := Read(pid, old_ts, w);
    call Yield();
    call End(pid, ts);
}

yield procedure {:layer 4} WriteClient({:linear} pid: One ProcessId, value: Value)
{
    var old_ts: TimeStamp;
    var {:layer 2, 4} w: ReplicaSet;
    var ts: TimeStamp;

    call old_ts, w := Begin(pid);
    call Yield();
    call ts := Write(pid, value, old_ts, w);
    call Yield();
    call End(pid, ts);
}

yield procedure {:layer 3} Begin({:linear} pid: One ProcessId) returns (ts: TimeStamp, {:layer 2, 3} w: ReplicaSet)
refines action {:layer 4} _ {
    ts := TS;
 }
{
    call ts, w := Begin#2(pid);
}

yield procedure {:layer 3} Read({:linear} pid: One ProcessId, old_ts: TimeStamp, {:layer 2, 3} w: ReplicaSet) returns (ts: TimeStamp, value: Value)
refines action {:layer 4} _ { 
    assume le(old_ts, ts);
    assume Map_Contains(value_store, ts);
    value := Map_At(value_store, ts);
}
{
    var q: ReplicaSet;

    call ts, value, q := QueryPhase(old_ts, w);
    call UpdatePhase(ts, value);
}

yield procedure {:layer 3} Write({:linear} pid: One ProcessId, value: Value, old_ts: TimeStamp, {:layer 2, 3} w: ReplicaSet) returns (ts: TimeStamp)
refines action {:layer 4} _ {
    assume lt(old_ts, ts);
    assume !Map_Contains(value_store, ts);
    value_store := Map_Update(value_store, ts, value);
}
{
    var _q: ReplicaSet;
    var _value: Value;

    call ts, _value, _q := QueryPhase(old_ts, w);
    ts := TimeStamp(ts->t + 1, pid->val);
    call {:layer 1} last_write := Copy(last_write[ts->pid := ts->t]);
    call AddToValueStore(ts, value);
    call UpdatePhase(ts, value);
}

yield right procedure {:layer 3} QueryPhase({:layer 2, 3} old_ts: TimeStamp, {:layer 2, 3} w: ReplicaSet) returns (max_ts: TimeStamp, max_value: Value, q: ReplicaSet)
{
    assume IsQuorum(q);
    call max_ts, max_value := QueryPhaseHelper(0, q, old_ts, w);
}

yield right procedure {:layer 3} QueryPhaseHelper(i: int, q: ReplicaSet, {:layer 2, 3} old_ts: TimeStamp, {:layer 2, 3} w: ReplicaSet) returns (max_ts: TimeStamp, max_value: Value)
{
    var ts: TimeStamp;
    var value: Value;

    if (i == numReplicas)
    {
        max_ts := LeastTimeStamp();
        return;
    }
    par ts, value := Query#2(i, q, old_ts, w) | max_ts, max_value := QueryPhaseHelper(i + 1, q, old_ts, w);
    if (lt(max_ts, ts))
    {
        max_ts := ts;
        max_value := value;
    }
}

yield left procedure {:layer 3} UpdatePhase(ts: TimeStamp, value: Value)
{
    var q: ReplicaSet;

    assume IsQuorum(q);
    call UpdatePhaseHelper(0, ts, value, q);
}

yield left procedure {:layer 3} UpdatePhaseHelper(i: int, ts: TimeStamp, value: Value, q: ReplicaSet)
{
    if (i == numReplicas)
    {
        return;
    }
    par Update#2(i, ts, value, q) | UpdatePhaseHelper(i + 1, ts, value, q);
}

yield procedure {:layer 2} Begin#2({:linear} pid: One ProcessId) returns (ts: TimeStamp, {:layer 2} w: ReplicaSet)
refines action {:layer 3} _ {
    ts := TS;
    assume (forall rid: ReplicaId :: w[rid] ==> le(ts, replica_ts[rid]));
}
{
    call ts := Begin#0(pid);
    call {:layer 2} w := CalculateQuorum(replica_ts, ts);
}

pure procedure {:inline 1} CalculateQuorum(replica_ts: [ReplicaId]TimeStamp, ts: TimeStamp) returns (w: ReplicaSet)
{
    // calculate the set of all replica ids whose timestamp is at least ts
    w := (lambda rid: ReplicaId:: IsReplica(rid) && le(ts, replica_ts[rid]));
}

yield procedure {:layer 2} Query#2(rid: ReplicaId, q: ReplicaSet, {:layer 2} old_ts: TimeStamp, {:layer 2} w: ReplicaSet) returns (ts: TimeStamp, value: Value)
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
    }
}
{
    if (q[rid])
    {
        call ts, value := Query#1(rid);
    }
    else
    {
        ts := LeastTimeStamp();
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
{
    if (q[rid])
    {
        call Update#1(rid, ts, value);
    }
}

yield procedure {:layer 1} Query#1(rid: ReplicaId) returns (ts: TimeStamp, value: Value)
refines action {:layer 2} _ {
    ts := replica_ts[rid];
    assume Map_Contains(value_store, ts);
    value := Map_At(value_store, ts);
}
{
    call ts, value := Query#0(rid);
}

yield procedure {:layer 1} AddToValueStore(ts: TimeStamp, value: Value)
refines action {:layer 2, 3} _ {
    assume !Map_Contains(value_store, ts);
    value_store := Map_Update(value_store, ts, value);
}
{
    call {:layer 1} value_store := Copy(Map_Update(value_store, ts, value));
}

yield procedure {:layer 1} Update#1(rid: ReplicaId, ts: TimeStamp, value: Value)
refines action {:layer 2} _ {
    if (lt(replica_ts[rid], ts)) {
        replica_ts[rid] := ts;
    }
}
{
    call Update#0(rid, ts, value);
    call {:layer 1} replica_ts := Copy(replica_ts[rid := replica_store[rid]->ts]);
}

yield procedure {:layer 0} Begin#0({:linear} pid: One ProcessId) returns (ts: TimeStamp);
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

yield procedure {:layer 0} End({:linear} pid: One ProcessId, ts: TimeStamp);
refines action {:layer 1, 4} _ {
    if (lt(TS, ts)) {
        TS := ts;
    }
}
