// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// In this example we show how to model a reader-writer lock.

type {:linear "tid"} Tid;

type {:datatype} Option _;
function {:constructor} None<T>(): Option T;
function {:constructor} Some<T>(t: T): Option T;

function {:inline} EmptySet<T>(): [T]bool
{
    MapConst(false)
}


// An `RwLock` allows either a number of `readers` or at most one `writer` at
// any point in time.
type {:datatype} RwLock;
function {:constructor} RwLock(writer: Option Tid, readers: [Tid]bool): RwLock;

// We want to obtain the following mover types.
// * Acquiring a read or write lock is a right mover.
// * Releasing a read or write lock is a left mover.
// * Actions that read while holding a read lock and actions that write while
//   holding a write lock are both (left and right) movers.

////////////////////////////////////////////////////////////////////////////////

var {:layer 0, 1} rwlock: RwLock;

// Acquiring a read lock is possible if there is no writer, and has the effect
// of adding us to `readers`.
procedure {:right}{:layer 1, 1} atomic_acquire_read({:linear "tid"} tid: Tid)
modifies rwlock;
{
    assume writer#RwLock(rwlock) == None();
    rwlock := RwLock(writer#RwLock(rwlock), readers#RwLock(rwlock)[tid := true]);
}

// Acquiring a write lock is possbile if there is no other writer and no reader,
// and has the effect of storing us as the `writer`.
procedure {:right}{:layer 1, 1} atomic_acquire_write({:linear "tid"} tid: Tid)
modifies rwlock;
{
    assume writer#RwLock(rwlock) == None();
    assume readers#RwLock(rwlock) == EmptySet();
    rwlock := RwLock(Some(tid), readers#RwLock(rwlock));
}

// The predicate for holding a read lock:
// There is no writer and we are among the readers.
function {:inline} holds_read_lock(tid: Tid, rwlock: RwLock): bool
{
    writer#RwLock(rwlock) == None() &&
    readers#RwLock(rwlock)[tid]
}

// The predicate for holding a write lock:
// We are the writer and there are no readers.
function {:inline} holds_write_lock(tid: Tid, rwlock: RwLock): bool
{
    writer#RwLock(rwlock) == Some(tid) &&
    readers#RwLock(rwlock) == EmptySet()
}

// Releasing a read lock takes us out of `readers`.
procedure {:left}{:layer 1, 1} atomic_release_read({:linear "tid"} tid: Tid)
modifies rwlock;
{
    assert holds_read_lock(tid, rwlock);
    rwlock := RwLock(writer#RwLock(rwlock), readers#RwLock(rwlock)[tid := false]);
}

// Releasing a write lock takes us out of `writer`.
procedure {:left}{:layer 1, 1} atomic_release_write({:linear "tid"} tid: Tid)
modifies rwlock;
{
    assert holds_write_lock(tid, rwlock);
    rwlock := RwLock(None(), readers#RwLock(rwlock));
}

procedure {:yields}{:layer 0}{:refines "atomic_acquire_read"} acquire_read({:linear "tid"} tid: Tid);
procedure {:yields}{:layer 0}{:refines "atomic_release_read"} release_read({:linear "tid"} tid: Tid);
procedure {:yields}{:layer 0}{:refines "atomic_acquire_write"} acquire_write({:linear "tid"} tid: Tid);
procedure {:yields}{:layer 0}{:refines "atomic_release_write"} release_write({:linear "tid"} tid: Tid);

////////////////////////////////////////////////////////////////////////////////

// The following actions read from and write to a single memory location,
// respectively, protected by gates that state that we are holding a read and
// write lock, respectively. As desired, we can prove that these actions are
// both movers.

type Addr;
type Val;

var {:layer 0, 2} memory: [Addr]Val;

procedure {:both}{:layer 1,1} atomic_read({:linear "tid"} tid: Tid, a: Addr) returns (v: Val)
{
    assert holds_read_lock(tid, rwlock);
    v := memory[a];
}

procedure {:both}{:layer 1,1} atomic_write({:linear "tid"} tid: Tid, a: Addr, v: Val)
modifies memory;
{
    assert holds_write_lock(tid, rwlock);
    memory[a] := v;
}

procedure {:yields}{:layer 0}{:refines "atomic_read"} read({:linear "tid"} tid: Tid, a: Addr) returns (v: Val);
procedure {:yields}{:layer 0}{:refines "atomic_write"} write({:linear "tid"} tid: Tid, a: Addr, v: Val);

////////////////////////////////////////////////////////////////////////////////

// Now we can write client procedure that read from and write to two memory
// locations inside a critical section while holding the appropriate lock.
// Notice that (at layer 1) there are no yield points between calls, due to the
// mover types of the callees.

procedure {:yields}{:layer 1}{:refines "atomic_read2"}
read2({:hide}{:linear "tid"} tid: Tid, a1: Addr, a2: Addr) returns (v1: Val, v2: Val)
{
    call acquire_read(tid);
    call v1 := read(tid, a1);
    call v2 := read(tid, a2);
    call release_read(tid);
}

procedure {:yields}{:layer 1}{:refines "atomic_write2"}
write2({:hide}{:linear "tid"} tid: Tid, a1: Addr, a2: Addr, v1: Val, v2: Val)
{
    call acquire_write(tid);
    call write(tid, a1, v1);
    call write(tid, a2, v2);
    call release_write(tid);
}

////////////////////////////////////////////////////////////////////////////////

// We can prove that the above procedures perform their operations on two memory
// locations atomically.

procedure {:atomic}{:layer 2} atomic_read2(a1: Addr, a2: Addr) returns (v1: Val, v2: Val)
{
    v1 := memory[a1];
    v2 := memory[a2];
}

procedure {:atomic}{:layer 2} atomic_write2(a1: Addr, a2:Addr, v1: Val, v2: Val)
modifies memory;
{
    memory[a1] := v1;
    memory[a2] := v2;
}
