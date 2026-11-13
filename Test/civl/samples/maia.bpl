type Value;
type SemId = int; 
type MemId = int;
type Tid = int;
const N: int; // maximum number of threads

// sharers contains the ids of threads that are allowed to read this immutable cell
datatype MemShare {
    mem_id: MemId,
    tid: Tid
}

datatype MemCell {
    val: Value,
    sharers: [One MemShare]bool,
}

// all cells in this map are immutable
// to read imm_mem[One(mem_id)], a capability in imm_mem[One(mem_id)]->sharers must be presented
var imm_mem: Map (One MemId) MemCell;

datatype SemWait {
    sem_id: SemId,
}

datatype SemSignal {
    sem_id: SemId,
    tid: Tid
}

datatype Semaphore {
    done: UnitMap (One SemSignal), // done signals
    wait_for: [One SemSignal]bool, // pending signals
    mem: Map (One MemId) Value,    // cells returned via a signal
    mem_shares: UnitMap (One MemShare) // mem shares returned via a signal
}

var semaphores: Map (One SemId) Semaphore;

/*
Starting thread receives semaphore map, wait map containing wait capability for each semaphore, and memory map.
Each semaphore contains all the signalers in done.
Before publishing a semaphore in the global semaphores map:
- remove requisite signal permissions from done 
- initialize wait_for with ordinary set of these removed permissions
Waiting on a semaphore uses the wait permission, blocks on wait_for becoming a subset of done.
Upon success, ownership of mem is returned.
A signaling thread moves its signal capability and any memory cells into the semaphore.
this thread must demonstrate that its signal capability is in the wait_for set.
Thus, semaphores provide a mechanism for transferring ownership of memory cells back and forth.

A thread that owns a memory can either transfer ownership to another thread via a parameter.
Or it can transfer ownership to the global pool of immutable cells, after suitable initialization.
When doing this transfer, the set of sharers is initialized.
A sharer must present a capability belonging to this set of sharers.
To remove ownership from imm_mem, all the capabilities must be presented as evidence.
These capabilities are retreived from a semaphore wait along with memory cells.
*/