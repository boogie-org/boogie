// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type X;
const nil: X;

var {:layer 0,2} b: bool;
var {:layer 1,3} lock: X;

yield procedure {:layer 3} Customer({:linear} tid: One X)
preserves call Yield(tid);
{
  while (*)
  invariant {:yields} true;
  invariant call Yield(tid);
  {
    call Enter(tid);
    call Leave(tid);
  }
}

function {:inline} InvLock(lock: X, b: bool) : bool
{ lock != nil <==> b }

yield invariant {:layer 2} Yield({:linear} tid: One X);
preserves tid->val != nil && InvLock(lock, b);

right action {:layer 3} AtomicEnter({:linear} tid: One X)
modifies lock;
{ assume lock == nil && tid->val != nil; lock := tid->val; }

yield procedure {:layer 2} Enter({:linear} tid: One X)
refines AtomicEnter;
preserves call Yield(tid);
{
  call LowerEnter(tid);
}

left action {:layer 3} AtomicLeave({:linear} tid: One X)
modifies lock;
{ assert lock == tid->val && tid->val != nil; lock := nil; }

yield procedure {:layer 2} Leave({:linear} tid: One X)
refines AtomicLeave;
preserves call Yield(tid);
{
  call LowerLeave();
}

atomic action {:layer 2} AtomicLowerEnter({:linear} tid: One X)
modifies b, lock;
{ assume !b; b := true; lock := tid->val; }

yield procedure {:layer 1} LowerEnter({:linear} tid: One X)
refines AtomicLowerEnter;
{
  var status: bool;

  while (true)
  invariant {:yields} true;
  {
    call status := CAS(false, true);
    if (status) {
      call {:layer 1} lock := Copy(tid->val);
      return;
    }
  }
}

atomic action {:layer 2} AtomicLowerLeave()
modifies b, lock;
{ b := false; lock := nil; }

yield procedure {:layer 1} LowerLeave()
refines AtomicLowerLeave;
{
  call SET(false);
  call {:layer 1} lock := Copy(nil);
}

atomic action {:layer 1} AtomicCAS(prev: bool, next: bool) returns (status: bool)
modifies b;
{
  if (b == prev) {
    b := next;
    status := true;
  } else {
    status := false;
  }
}

atomic action {:layer 1} AtomicSET(next: bool)
modifies b;
{ b := next; }

yield procedure {:layer 0} CAS(prev: bool, next: bool) returns (status: bool);
refines AtomicCAS;

yield procedure {:layer 0} SET(next: bool);
refines AtomicSET;
