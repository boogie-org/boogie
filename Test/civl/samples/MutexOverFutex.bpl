// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Tid; // thread identifiers

type Mutex = Option Tid;

datatype Futex { Futex(word: int, waiters:[Tid]bool) }

var {:layer 1, 2} mutex: Mutex;           // specification
var {:layer 1, 1} inSlowPath: [Tid]bool;  // auxiliary helper
var {:layer 0, 1} futex: Futex;           // implementation

/// Implementation of Mutex

atomic action {:layer 2} AtomicLock(tid: Lval Tid)
modifies mutex;
{
  assume mutex == None();
  mutex := Some(tid->val);
}
yield procedure {:layer 1} Lock(tid: Lval Tid)
refines AtomicLock;
preserves call YieldInv();
preserves call YieldWait(tid);
{
  var oldValue, temp: int;
  call oldValue := CmpXchg(0, 1);
  if (oldValue != 0) {
    call EnterSlowPath(tid);
    while (true)
    invariant {:yields} true;
    invariant call YieldInv();
    invariant call YieldWait(tid);
    invariant call YieldSlowPath(tid);
    {
      if (oldValue != 2) {
        call temp := CmpXchg(1, 2);
      }
      par YieldInv() | YieldWait(tid) | YieldSlowPath(tid);
      if (oldValue == 2 || temp != 0) {
        call WaitEnter(tid->val, 2);
        par YieldInv() | YieldSlowPath(tid);
        call WaitExit(tid->val);
      }
      par YieldInv() | YieldWait(tid) | YieldSlowPath(tid);
      call oldValue := CmpXchg(0, 2);
      if (oldValue == 0) {
        call ExitSlowPath(tid);
        break;
      }
    }
  }
  call SetMutex(Some(tid->val));
}

atomic action {:layer 2} AtomicUnlock(tid: Lval Tid)
modifies mutex;
{
  assert mutex == Some(tid->val);
  mutex := None();
}
yield procedure {:layer 1} Unlock(tid: Lval Tid)
refines AtomicUnlock;
preserves call YieldInv();
preserves call YieldWait(tid);
{
  var oldValue: int;
  call oldValue := FetchSub(1);
  if (oldValue == 1) {
    call SetMutex(None());
  } else {
    call EnterSlowPath(tid);
    par YieldInv() | YieldWait(tid) | YieldSlowPath(tid);
    call Store(0);
    call SetMutex(None());
    par YieldInv() | YieldWait(tid) | YieldSlowPath(tid);
    call Wake();
    call ExitSlowPath(tid);
  }
}

/// Yield invariants

function {:inline} IsValid(word: int): bool {
  word == 0 || word == 1 || word == 2
}

yield invariant {:layer 1} YieldInv();
invariant IsValid(futex->word);
invariant (forall i: Tid :: futex->waiters[i] ==> inSlowPath[i]);
invariant futex->word == 2 || futex->waiters == MapConst(false) || (exists i: Tid :: !futex->waiters[i] && inSlowPath[i]);
invariant mutex == None() <==> futex->word == 0;

yield invariant {:layer 1} YieldWait(tid: Lval Tid);
invariant !futex->waiters[tid->val];

yield invariant {:layer 1} YieldSlowPath(tid: Lval Tid);
invariant inSlowPath[tid->val];

/// Linking action for mutex

action {:layer 1, 1} SetMutex(x: Mutex)
modifies mutex;
{
  mutex := x;
}

/// Linking actions for inSlowPath

action {:layer 1, 1} EnterSlowPath(tid: Lval Tid)
modifies inSlowPath;
{
  inSlowPath[tid->val] := true;
}

action {:layer 1, 1} ExitSlowPath(tid: Lval Tid)
modifies inSlowPath;
{
  inSlowPath[tid->val] := false;
}

/// Primitive atomic actions

atomic action {:layer 1} AtomicCmpXchg(expected: int, newValue: int) returns (oldValue: int)
modifies futex;
{
  oldValue := futex->word;
  if (oldValue == expected) {
    futex->word := newValue;
  }
}
yield procedure {:layer 0} CmpXchg(expected: int, newValue: int) returns (oldValue: int);
refines AtomicCmpXchg;

atomic action {:layer 1} AtomicFetchSub(val: int) returns (oldValue: int)
modifies futex;
{
  oldValue := futex->word;
  futex->word := oldValue - 1;
}
yield procedure {:layer 0} FetchSub(val: int) returns (oldValue: int);
refines AtomicFetchSub;

atomic action {:layer 1} AtomicStore(val: int)
modifies futex;
{
  futex->word := val;
}
yield procedure {:layer 0} Store(val: int);
refines AtomicStore;

atomic action {:layer 1} AtomicWaitEnter(tid: Tid, val: int)
modifies futex;
{
  assert !futex->waiters[tid];
  if (futex->word == val) {
    futex->waiters[tid] := true;
  }
}
yield procedure {:layer 0} WaitEnter(tid: Tid, val: int);
refines AtomicWaitEnter;

atomic action {:layer 1} AtomicWaitExit(tid: Tid)
modifies futex;
{
  assume !futex->waiters[tid];
}
yield procedure {:layer 0} WaitExit(tid: Tid);
refines AtomicWaitExit;

atomic action {:layer 1} AtomicWake()
modifies futex;
{
  var tid: Tid;
  if (futex->waiters != MapConst(false)) {
    assume futex->waiters[tid];
    futex->waiters[tid] := false;
  }
}
yield procedure {:layer 0} Wake();
refines AtomicWake;
