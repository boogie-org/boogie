// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type X;
const nil: X;

var {:layer 0,2} b: bool;
var {:layer 1,3} lock: X;

procedure {:yields} {:layer 3} Customer({:linear "tid"} tid: X)
requires {:layer 2} tid != nil;
requires {:layer 2} InvLock(lock, b);
ensures {:layer 2} InvLock(lock, b);
{
  yield;
  assert {:layer 2} InvLock(lock, b);
  while (*)
  invariant {:layer 2} InvLock(lock, b);
  {
    call Enter(tid);
    call Leave(tid);
    yield;
    assert {:layer 2} InvLock(lock, b);
  }
  yield;
  assert {:layer 2} InvLock(lock, b);
}

function {:inline} InvLock(lock: X, b: bool) : bool
{ lock != nil <==> b }

procedure {:right} {:layer 3} AtomicEnter({:linear "tid"} tid: X)
modifies lock;
{ assume lock == nil && tid != nil; lock := tid; }

procedure {:yields} {:layer 2} {:refines "AtomicEnter"} Enter({:linear "tid"} tid: X)
requires {:layer 2} tid != nil;
requires {:layer 2} InvLock(lock, b);
ensures {:layer 2} InvLock(lock, b);
{
  yield;
  assert {:layer 2} InvLock(lock, b);
  call LowerEnter(tid);
  yield;
  assert {:layer 2} InvLock(lock, b);
}

procedure {:left} {:layer 3} AtomicLeave({:linear "tid"} tid:X)
modifies lock;
{ assert lock == tid && tid != nil; lock := nil; }

procedure {:yields} {:layer 2} {:refines "AtomicLeave"} Leave({:linear "tid"} tid:X)
requires {:layer 2} InvLock(lock, b);
ensures {:layer 2} InvLock(lock, b);
{
  yield;
  assert {:layer 2} InvLock(lock, b);
  call LowerLeave();
  yield;
  assert {:layer 2} InvLock(lock, b);
}

procedure {:atomic} {:layer 2} AtomicLowerEnter({:linear "tid"} tid: X)
modifies b, lock;
{ assume !b; b := true; lock := tid; }

procedure {:yields} {:layer 1} {:refines "AtomicLowerEnter"} LowerEnter({:linear "tid"} tid: X)
{
  var status: bool;
  yield;
  while (true) {
    call status := CAS(false, true);
    if (status) {
      call SetLock(tid);
      yield;
      return;
    }
    yield;
  }
  yield;
}

procedure {:atomic} {:layer 2} AtomicLowerLeave()
modifies b, lock;
{ b := false; lock := nil; }

procedure {:yields} {:layer 1} {:refines "AtomicLowerLeave"} LowerLeave()
{
  yield;
  call SET(false);
  call SetLock(nil);
  yield;
}

procedure {:layer 1} {:inline 1} SetLock(v: X)
modifies lock;
{ lock := v; }

procedure {:atomic} {:layer 1} AtomicCAS(prev: bool, next: bool) returns (status: bool)
modifies b;
{
  if (b == prev) {
    b := next;
    status := true;
  } else {
    status := false;
  }
}

procedure {:atomic} {:layer 1} AtomicSET(next: bool)
modifies b;
{ b := next; }

procedure {:yields} {:layer 0} {:refines "AtomicCAS"} CAS(prev: bool, next: bool) returns (status: bool);
procedure {:yields} {:layer 0} {:refines "AtomicSET"} SET(next: bool);

function {:builtin "MapConst"} MapConstBool(bool) : [X]bool;
function {:inline} {:linear "tid"} TidCollector(x: X) : [X]bool
{
  MapConstBool(false)[x := true]
}
