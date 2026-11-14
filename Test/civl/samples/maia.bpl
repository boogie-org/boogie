// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Value;
type SemId = int;
type MemId = int;
type Tid = int;

datatype MemShare {
    MemShare(mem_id: MemId, tid: Tid)
}

// imm_mem_shares contains the capabilities allowed to read this immutable cell
datatype SharedValue {
    SharedValue(val: Value, imm_mem_shares: [One MemShare]bool)
}

// All cells in imm_mem are immutable.
// Reading a cell requires a capability in its imm_mem_shares set.
var {:layer 0,1} {:linear} imm_mem: Map (One MemId) SharedValue;

// Capabilities to enable immutable sharing of memory locations
// Retrieved when a memory location is published into imm_mem
// Returned when the memory location extracted from imm_mem
var {:layer 0,1} {:linear} imm_mem_shares: UnitMap (One MemShare);

datatype SemWait {
    SemWait(sem_id: SemId)
}

datatype SemSignal {
    SemSignal(sem_id: SemId, tid: Tid)
}

datatype Semaphore {
    Semaphore(
        done: UnitMap (One SemSignal), // done signals
        awaited: [One SemSignal]bool,  // all awaited signals
        mem: Map (One MemId) Value,    // memory cells returned via a signal
        imm_mem_shares: UnitMap (One MemShare)) // immutable memory shares returned via a signal
}

var {:layer 0,1} {:linear} semaphores: Map (One SemId) Semaphore;

// Capabilities required to signal a semaphore
// Retrieved when a semaphore is published into semaphores
// Returned when a semaphore wait succeeds
var {:layer 0,1} {:linear} sem_signals: UnitMap (One SemSignal);

/*
A thread starting a MAIA kernel receives a linear map containing wait capability for each semaphore,
and and a linear map containing memory values.
A semaphore is published into the global semaphores map by the Publish operation.
Before publishing a semaphore:
- remove requisite signal permissions from sem_signals
- initialize awaited with the ordinary set of these removed permissions
The published semaphore starts with empty done, mem, and imm_mem_shares maps and the awaited set.
Publish returns the removed signal permissions for distribution to signaling threads.
*/

yield invariant {:layer 1} SemaphorePublishInv({:linear} one_sem_id: One SemId);
preserves (forall tid: Tid:: Set_Contains(sem_signals->dom, One(SemSignal(one_sem_id->val, tid))));

yield invariant {:layer 1} SemaphoreInv();
preserves (forall one_sem_id: One SemId:: Map_Contains(semaphores, one_sem_id) ==> 
    (forall tid: Tid:: Set_Contains(
        Set_Union(Map_At(semaphores, one_sem_id)->awaited, sem_signals->dom),
        One(SemSignal(one_sem_id->val, tid)))));

atomic action {:layer 1} Publish({:linear_in} one_sem_id: One SemId,
                               awaited: [One SemSignal]bool)
    returns ({:linear} signals: UnitMap (One SemSignal))
modifies semaphores, sem_signals;
{
    var sem: Semaphore;
    var done: UnitMap (One SemSignal);
    var mem: Map (One MemId) Value;
    var shares: UnitMap (One MemShare);

    assert (forall signal: One SemSignal ::
        awaited[signal] ==> signal->val->sem_id == one_sem_id->val);
    call signals := Map_Split(sem_signals, awaited);
    call done := Map_MakeEmpty();
    call mem := Map_MakeEmpty();
    call shares := Map_MakeEmpty();
    sem := Semaphore(done, awaited, mem, shares);
    call Map_Put(semaphores, one_sem_id, sem);
}

/*
A signaling thread moves its signal capability and any memory cells into the semaphore.
This thread must demonstrate that its signal capability is in the awaited set.
Thus, semaphores provide a mechanism for transferring ownership of memory cells back and forth.
*/

atomic action {:layer 1} Signal({:linear_in} x: One SemSignal, {:linear_in} m: Map (One MemId) Value,
                              {:linear_in} s: UnitMap (One MemShare))
modifies semaphores;
{
    var one_sem_id: One SemId;

    one_sem_id := One(x->val->sem_id);
    assert Map_Contains(semaphores, one_sem_id);
    assert Set_Contains(Map_At(semaphores, one_sem_id)->awaited, x);
    call One_Put(semaphores->val[one_sem_id]->done, x);
    call Map_Join(semaphores->val[one_sem_id]->mem, m);
    call Map_Join(semaphores->val[one_sem_id]->imm_mem_shares, s);
}

/*
Waiting on a semaphore uses the wait permission and blocks on awaited becoming a subset of done.
Upon success, ownership of mem and mem_shares is returned.
Completed signal capabilities are returned to sem_signals.
*/

atomic action {:layer 1} Wait({:linear} x: One SemWait)
    returns ({:linear} one_sem_id: One SemId, {:linear} mem: Map (One MemId) Value,
             {:linear} mem_shares: UnitMap (One MemShare))
modifies semaphores, sem_signals;
{
    var sem: Semaphore;
    var done: UnitMap (One SemSignal);
    var awaited: [One SemSignal]bool;

    one_sem_id := One(x->val->sem_id);
    assert Map_Contains(semaphores, one_sem_id);
    call sem := Map_Get(semaphores, one_sem_id);
    Semaphore(done, awaited, mem, mem_shares) := sem;
    assume Set_IsSubset(awaited, done->dom);
    call Map_Join(sem_signals, done);
}

/*
A thread that owns a memory can either transfer ownership to another thread via a parameter.
Or it can transfer ownership to the global pool of immutable cells.
When doing this transfer, the set of sharers is initialized.
A sharer must present a capability belonging to this set of sharers to read the value.
To remove ownership from imm_mem, all the capabilities must be presented as evidence.
*/

yield invariant {:layer 1} ImmMemPublishInv({:linear} one_mem_id: One MemId);
preserves (forall tid: Tid:: Set_Contains(imm_mem_shares->dom, One(MemShare(one_mem_id->val, tid))));

yield invariant {:layer 1} ImmMemInv();
preserves (forall one_mem_id: One MemId:: Map_Contains(imm_mem, one_mem_id) ==>
    (forall tid: Tid:: Set_Contains(
        Set_Union(Map_At(imm_mem, one_mem_id)->imm_mem_shares, imm_mem_shares->dom),
        One(MemShare(one_mem_id->val, tid)))));

atomic action {:layer 1} MoveToShared({:linear_in} one_mem_id: One MemId, val: Value,
                                    ord_shares: [One MemShare]bool)
    returns ({:linear} lin_shares: UnitMap (One MemShare))
modifies imm_mem, imm_mem_shares;
{
    var shared_value: SharedValue;

    assert (forall share: One MemShare ::
        ord_shares[share] ==> share->val->mem_id == one_mem_id->val);
    call lin_shares := Map_Split(imm_mem_shares, ord_shares);
    shared_value := SharedValue(val, ord_shares);
    call Map_Put(imm_mem, one_mem_id, shared_value);
}

/*
MoveFromShared requires all of the cell's read capabilities in the supplied shares map.
It returns all supplied capabilities to imm_mem_shares for reuse, removes the cell
from imm_mem, and returns ownership of the cell and its value.
*/

atomic action {:layer 1} MoveFromShared(mem_id: MemId, {:linear_in} lin_shares: UnitMap (One MemShare))
    returns ({:linear} one_mem_id: One MemId, val: Value)
modifies imm_mem, imm_mem_shares;
{
    var shared_value: SharedValue;

    one_mem_id := One(mem_id);
    call shared_value := Map_Get(imm_mem, one_mem_id);
    assert Set_IsSubset(shared_value->imm_mem_shares, lin_shares->dom);
    call Map_Join(imm_mem_shares, lin_shares);
    val := shared_value->val;
}

atomic action {:layer 1} ReadFromShared({:linear} share: One MemShare) returns (val: Value)
{
    assert Map_Contains(imm_mem, One(share->val->mem_id));
    assert Set_Contains(Map_At(imm_mem, One(share->val->mem_id))->imm_mem_shares, share);
    val := Map_At(imm_mem, One(share->val->mem_id))->val;
}
