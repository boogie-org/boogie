// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Value = int;
type SemId = int;
type MemId = int;
type Tid = int;

datatype MemShare {
    MemShare(mem_id: MemId, tid: Tid)
}

// imm_mem_shares contains the identities of the capabilities allowed to read this immutable cell.
datatype SharedValue {
    SharedValue(val: Value, imm_mem_shares: [One MemShare]bool)
}

function {:inline} AllMemShares(mem_id: One MemId, shares: UnitMap (One MemShare)): bool {
    (forall tid: Tid:: Set_Contains(shares->dom, One(MemShare(mem_id->val, tid))))
}

// All cells in imm_mem are immutable.
// Reading a cell requires a capability in its imm_mem_shares set.
var {:layer 0,1} {:linear} imm_mem: Map (One MemId) SharedValue;

datatype SemWait {
    SemWait(sem_id: SemId)
}

datatype SemSignal {
    SemSignal(sem_id: SemId, tid: Tid)
}

datatype Semaphore {
    Semaphore(
        done: UnitMap (One SemSignal), // done signals
        awaited: [One SemSignal]bool, // all awaited signals
        mem: Map (One MemId) Value, // memory cells returned via a signal
        expected_mem_ids: Map SemSignal ([One MemId]bool), // memory addresses expected to be returned via a signal
        imm_mem_shares: UnitMap (One MemShare), // immutable memory shares returned via a signal
        expected_mem_shares: Map SemSignal ([One MemShare]bool)) // memory shares expected to be returned via a signal
}

function {:inline} AllSemaphoreSignals(sem_id: One SemId, signals: UnitMap (One SemSignal)): bool {
    (forall tid: Tid:: Set_Contains(signals->dom, One(SemSignal(sem_id->val, tid))))
}

var {:layer 0,1} {:linear} semaphores: Map (One SemId) Semaphore;

/*
A MAIA kernel receives ownership of one or more semaphore ids,
including the associated wait and signal capabilities.
It also receives ownership of memory locations and memory shares.
These resources are linear: ownership can be transferred but not duplicated.
Signal capabilities are indexed by semaphore id and thread id;
memory shares are indexed by memory id and thread id.
AllSemaphoreSignals and AllMemShares describe possession of all capabilities
for a given semaphore or memory id. These are predicates on caller-owned maps,
not global pools of capabilities.

Publish transfers a semaphore id into the global semaphores map.
The caller supplies the awaited signal identities and, for each signal,
the memory ids and memory shares expected to be returned.
All awaited signals must belong to this semaphore.
The semaphore starts with empty done, memory, and memory-share maps.
Publishing neither creates nor transfers signal capabilities;
the caller distributes its existing capabilities to signaling threads.

A signaling thread must own its signal capability and demonstrate that
the signal is in the published semaphore's awaited set.
Signal transfers the capability into done and transfers the supplied memory
and memory shares into the semaphore.
SemaphoreInv requires that each completed signal's expected resources
are present in the semaphore. Clients must establish and preserve this invariant,
using their own invariants to relate each thread's resources to those expected.
Thus, semaphores transfer ownership of memory resources between threads.

Wait retains the wait capability and blocks until all awaited signals are done.
It removes the semaphore from the global map and returns ownership of its id,
completed signal capabilities, memory, and memory shares.
SemaphoreWaitInv records that the semaphore is published; ExpectedSemaphoreContentsInv keeps
its awaited set and expected-resource maps fixed while the caller waits.
Together with SemaphoreInv, these facts let the caller recover the expected
resources. Returned signal capabilities can be combined with those retained
by the caller to publish and use the semaphore again.

A thread owning a memory location can transfer it directly to another thread,
or use MoveToShared to publish its id and value into imm_mem.
The caller supplies a set of authorized memory-share identities, all belonging
to that location. Publishing does not create or transfer memory shares;
the caller distributes its existing shares to readers.
ReadFromShared requires an authorized share and retains it.
SharedReadInv records that the location remains published and the share
remains authorized, so readers can access the immutable value across yields.

To regain exclusive ownership, a thread collects all authorized shares,
possibly using signals and a wait to recover shares held by other threads.
ExpectedImmMemContentsInv keeps the authorized set fixed while a share is held.
ReclaimMemIdInv records that the location is published, its authorized set
is nonempty, and all authorized shares are in the supplied linear map.
MoveFromShared checks possession of all authorized shares, removes the cell
from imm_mem, and returns its id and value. It retains the supplied shares,
which can be reused in a later sharing round.
*/

yield invariant {:layer 1} ExpectedSemaphoreContentsInv(
    {:linear} wait: One SemWait, awaited: [One SemSignal]bool,
    expected_mem_ids: Map SemSignal ([One MemId]bool),
    expected_mem_shares: Map SemSignal ([One MemShare]bool));
preserves Map_Contains(semaphores, One(wait->val->sem_id));
preserves Map_At(semaphores, One(wait->val->sem_id))->awaited == awaited;
preserves Map_At(semaphores, One(wait->val->sem_id))->expected_mem_ids == expected_mem_ids;
preserves Map_At(semaphores, One(wait->val->sem_id))->expected_mem_shares == expected_mem_shares;

yield invariant {:layer 1} SemaphoreInv();
preserves (forall one_sem_id: One SemId:: Map_Contains(semaphores, one_sem_id) ==>
    (var sem := Map_At(semaphores, one_sem_id);
     (forall signal: One SemSignal:: Map_Contains(sem->done, signal) && Map_Contains(sem->expected_mem_ids, signal->val) ==>
        Set_IsSubset(Map_At(sem->expected_mem_ids, signal->val), sem->mem->dom))));
preserves (forall one_sem_id: One SemId:: Map_Contains(semaphores, one_sem_id) ==>
    (var sem := Map_At(semaphores, one_sem_id);
     (forall signal: One SemSignal:: Map_Contains(sem->done, signal) && Map_Contains(sem->expected_mem_shares, signal->val) ==>
        Set_IsSubset(Map_At(sem->expected_mem_shares, signal->val), sem->imm_mem_shares->dom))));

yield procedure {:layer 0} Publish({:linear_in} sem_id: One SemId,
                               awaited: [One SemSignal]bool,
                               expected_mem_ids: Map SemSignal ([One MemId]bool),
                               expected_mem_shares: Map SemSignal ([One MemShare]bool));
refines atomic action {:layer 1} _
{
    var sem: Semaphore;
    var done: UnitMap (One SemSignal);
    var mem: Map (One MemId) Value;
    var shares: UnitMap (One MemShare);

    assert (forall signal: One SemSignal ::
        awaited[signal] ==> signal->val->sem_id == sem_id->val);
    call done := Map_MakeEmpty();
    call mem := Map_MakeEmpty();
    call shares := Map_MakeEmpty();
    sem := Semaphore(done, awaited, mem, expected_mem_ids, shares, expected_mem_shares);
    call Map_Put(semaphores, sem_id, sem);
}

yield invariant {:layer 1} SemaphoreSignalInv({:linear} signal: One SemSignal);
preserves Map_Contains(semaphores, One(signal->val->sem_id));
preserves Set_Contains(Map_At(semaphores, One(signal->val->sem_id))->awaited, signal);
free preserves !Map_Contains(Map_At(semaphores, One(signal->val->sem_id))->done, signal);

yield procedure {:layer 0} Signal({:linear_in} signal: One SemSignal, {:linear_in} m: Map (One MemId) Value,
                              {:linear_in} s: UnitMap (One MemShare));
refines atomic action {:layer 1} _
{
    var one_sem_id: One SemId;

    one_sem_id := One(signal->val->sem_id);
    assert Map_Contains(semaphores, one_sem_id);
    assert Set_Contains(Map_At(semaphores, one_sem_id)->awaited, signal);
    call One_Put(semaphores->val[one_sem_id]->done, signal);
    call Map_Join(semaphores->val[one_sem_id]->mem, m);
    call Map_Join(semaphores->val[one_sem_id]->imm_mem_shares, s);
}

yield invariant {:layer 1} SemaphoreWaitInv({:linear} wait: One SemWait);
preserves Map_Contains(semaphores, One(wait->val->sem_id));

yield procedure {:layer 0} Wait({:linear} wait: One SemWait)
    returns ({:linear} one_sem_id: One SemId, {:linear} done: UnitMap (One SemSignal),
             {:linear} mem: Map (One MemId) Value, {:linear} mem_shares: UnitMap (One MemShare));
refines atomic action {:layer 1} _
{
    var sem: Semaphore;
    var awaited: [One SemSignal]bool;
    var expected_mem_ids: Map SemSignal ([One MemId]bool);
    var expected_mem_shares: Map SemSignal ([One MemShare]bool);

    one_sem_id := One(wait->val->sem_id);
    call sem := Map_Get(semaphores, one_sem_id);
    Semaphore(done, awaited, mem, expected_mem_ids, mem_shares, expected_mem_shares) := sem;
    assume Set_IsSubset(awaited, done->dom);
}

yield invariant {:layer 1} SharedReadInv({:linear} share: One MemShare);
preserves Map_Contains(imm_mem, One(share->val->mem_id));
preserves Set_Contains(Map_At(imm_mem, One(share->val->mem_id))->imm_mem_shares, share);

yield procedure {:layer 0} ReadFromShared({:linear} share: One MemShare) returns (val: Value);
refines atomic action {:layer 1} _
{
    assert Map_Contains(imm_mem, One(share->val->mem_id));
    assert Set_Contains(Map_At(imm_mem, One(share->val->mem_id))->imm_mem_shares, share);
    val := Map_At(imm_mem, One(share->val->mem_id))->val;
}

yield procedure {:layer 0} MoveToShared({:linear_in} one_mem_id: One MemId, val: Value,
                                    ord_shares: [One MemShare]bool);
refines atomic action {:layer 1} _
{
    var shared_value: SharedValue;

    assert (forall share: One MemShare ::
        ord_shares[share] ==> share->val->mem_id == one_mem_id->val);
    shared_value := SharedValue(val, ord_shares);
    call Map_Put(imm_mem, one_mem_id, shared_value);
}

yield invariant {:layer 1} ExpectedImmMemContentsInv(
    {:linear} share: One MemShare, shares: [One MemShare]bool);
preserves shares[share];
preserves Map_Contains(imm_mem, One(share->val->mem_id));
preserves Map_At(imm_mem, One(share->val->mem_id))->imm_mem_shares == shares;

yield invariant {:layer 1} ReclaimMemIdInv(
    mem_id: MemId, {:linear} shares: UnitMap (One MemShare));
preserves Map_Contains(imm_mem, One(mem_id));
preserves Map_At(imm_mem, One(mem_id))->imm_mem_shares != Set_Empty();
preserves Set_IsSubset(Map_At(imm_mem, One(mem_id))->imm_mem_shares, shares->dom);

/*
MoveFromShared requires all of the cell's read capabilities in the supplied shares map.
It removes the cell from imm_mem and returns ownership of the cell and its value.
*/
yield procedure {:layer 0} MoveFromShared(mem_id: MemId, {:linear} shares: UnitMap (One MemShare))
    returns ({:linear} one_mem_id: One MemId, val: Value);
refines atomic action {:layer 1} _
{
    var shared_value: SharedValue;

    one_mem_id := One(mem_id);
    call shared_value := Map_Get(imm_mem, one_mem_id);
    assert Set_IsSubset(shared_value->imm_mem_shares, shares->dom);
    val := shared_value->val;
}
