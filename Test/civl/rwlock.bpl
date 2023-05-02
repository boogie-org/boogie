// RUN: %parallel-boogie /lib:base "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// In this example we show how to model a reader-writer lock.

type {:linear "tid"} Tid;

function {:inline} EmptySet<T>(): [T]bool
{
    MapConst(false)
}


// An `RwLock` allows either a number of `readers` or at most one `writer` at
// any point in time.
datatype RwLock { RwLock(writer: Option Tid, readers: [Tid]bool) }

// We want to obtain the following mover types.
// * Acquiring a read or write lock is a right mover.
// * Releasing a read or write lock is a left mover.
// * Actions that read while holding a read lock and actions that write while
//   holding a write lock are both (left and right) movers.

////////////////////////////////////////////////////////////////////////////////

var {:layer 0, 1} rwlock: RwLock;

// Acquiring a read lock is possible if there is no writer, and has the effect
// of adding us to `readers`.
-> action {:layer 1, 1} atomic_acquire_read({:linear "tid"} tid: Tid)
modifies rwlock;
{
    assume rwlock->writer == None();
    rwlock := RwLock(rwlock->writer, rwlock->readers[tid := true]);
}

// Acquiring a write lock is possbile if there is no other writer and no reader,
// and has the effect of storing us as the `writer`.
-> action {:layer 1, 1} atomic_acquire_write({:linear "tid"} tid: Tid)
modifies rwlock;
{
    assume rwlock->writer == None();
    assume rwlock->readers == EmptySet();
    rwlock := RwLock(Some(tid), rwlock->readers);
}

// The predicate for holding a read lock:
// There is no writer and we are among the readers.
function {:inline} holds_read_lock(tid: Tid, rwlock: RwLock): bool
{
    rwlock->writer == None() &&
    rwlock->readers[tid]
}

// The predicate for holding a write lock:
// We are the writer and there are no readers.
function {:inline} holds_write_lock(tid: Tid, rwlock: RwLock): bool
{
    rwlock->writer == Some(tid) &&
    rwlock->readers == EmptySet()
}

// Releasing a read lock takes us out of `readers`.
<- action {:layer 1, 1} atomic_release_read({:linear "tid"} tid: Tid)
modifies rwlock;
{
    assert holds_read_lock(tid, rwlock);
    rwlock := RwLock(rwlock->writer, rwlock->readers[tid := false]);
}

// Releasing a write lock takes us out of `writer`.
<- action {:layer 1, 1} atomic_release_write({:linear "tid"} tid: Tid)
modifies rwlock;
{
    assert holds_write_lock(tid, rwlock);
    rwlock := RwLock(None(), rwlock->readers);
}

yield procedure {:layer 0} acquire_read({:linear "tid"} tid: Tid);
refines atomic_acquire_read;

yield procedure {:layer 0} release_read({:linear "tid"} tid: Tid);
refines atomic_release_read;

yield procedure {:layer 0} acquire_write({:linear "tid"} tid: Tid);
refines atomic_acquire_write;

yield procedure {:layer 0} release_write({:linear "tid"} tid: Tid);
refines atomic_release_write;

////////////////////////////////////////////////////////////////////////////////

// The following actions read from and write to a single memory location,
// respectively, protected by gates that state that we are holding a read and
// write lock, respectively. As desired, we can prove that these actions are
// both movers.

type Addr;
type Val;

var {:layer 0, 2} memory: [Addr]Val;

<-> action {:layer 1,1} atomic_read({:linear "tid"} tid: Tid, a: Addr) returns (v: Val)
{
    assert holds_read_lock(tid, rwlock);
    v := memory[a];
}

<-> action {:layer 1,1} atomic_write({:linear "tid"} tid: Tid, a: Addr, v: Val)
modifies memory;
{
    assert holds_write_lock(tid, rwlock);
    memory[a] := v;
}

yield procedure {:layer 0} read({:linear "tid"} tid: Tid, a: Addr) returns (v: Val);
refines atomic_read;

yield procedure {:layer 0} write({:linear "tid"} tid: Tid, a: Addr, v: Val);
refines atomic_write;

////////////////////////////////////////////////////////////////////////////////

// Now we can write client procedure that read from and write to two memory
// locations inside a critical section while holding the appropriate lock.
// Notice that (at layer 1) there are no yield points between calls, due to the
// mover types of the callees.

yield procedure {:layer 1}
read2({:hide}{:linear "tid"} tid: Tid, a1: Addr, a2: Addr) returns (v1: Val, v2: Val)
refines atomic_read2;
{
    call acquire_read(tid);
    call v1 := read(tid, a1);
    call v2 := read(tid, a2);
    call release_read(tid);
}

yield procedure {:layer 1}
write2({:hide}{:linear "tid"} tid: Tid, a1: Addr, a2: Addr, v1: Val, v2: Val)
refines atomic_write2;
{
    call acquire_write(tid);
    call write(tid, a1, v1);
    call write(tid, a2, v2);
    call release_write(tid);
}

////////////////////////////////////////////////////////////////////////////////

// We can prove that the above procedures perform their operations on two memory
// locations atomically.

>-< action {:layer 2} atomic_read2(a1: Addr, a2: Addr) returns (v1: Val, v2: Val)
{
    v1 := memory[a1];
    v2 := memory[a2];
}

>-< action {:layer 2} atomic_write2(a1: Addr, a2:Addr, v1: Val, v2: Val)
modifies memory;
{
    memory[a1] := v1;
    memory[a2] := v2;
}
