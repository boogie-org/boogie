// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "tid"} X;
const nil: X;

var {:layer 0,2} b: bool;
var {:layer 1,3} lock: X;

procedure {:yields} {:layer 3}
{:yield_preserves "Yield", tid}
Customer({:linear "tid"} tid: X)
{
  while (*)
  invariant {:yields} {:layer 1,2,3} {:yield_loop "Yield", tid} true;
  {
    call Enter(tid);
    call Leave(tid);
  }
}

function {:inline} InvLock(lock: X, b: bool) : bool
{ lock != nil <==> b }

procedure {:yield_invariant} {:layer 2} Yield({:linear "tid"} tid: X);
requires tid != nil && InvLock(lock, b);

procedure {:right} {:layer 3} AtomicEnter({:linear "tid"} tid: X)
modifies lock;
{ assume lock == nil && tid != nil; lock := tid; }

procedure {:yields} {:layer 2} {:refines "AtomicEnter"}
{:yield_preserves "Yield", tid}
Enter({:linear "tid"} tid: X)
{
  call LowerEnter(tid);
}

procedure {:left} {:layer 3} AtomicLeave({:linear "tid"} tid:X)
modifies lock;
{ assert lock == tid && tid != nil; lock := nil; }

procedure {:yields} {:layer 2} {:refines "AtomicLeave"}
{:yield_preserves "Yield", tid}
Leave({:linear "tid"} tid:X)
{
  call LowerLeave();
}

procedure {:atomic} {:layer 2} AtomicLowerEnter({:linear "tid"} tid: X)
modifies b, lock;
{ assume !b; b := true; lock := tid; }

procedure {:yields} {:layer 1} {:refines "AtomicLowerEnter"} LowerEnter({:linear "tid"} tid: X)
{
  var status: bool;

  while (true)
  invariant {:yields} {:layer 1} true;
  {
    call status := CAS(false, true);
    if (status) {
      call SetLock(tid);
      return;
    }
  }
}

procedure {:atomic} {:layer 2} AtomicLowerLeave()
modifies b, lock;
{ b := false; lock := nil; }

procedure {:yields} {:layer 1} {:refines "AtomicLowerLeave"} LowerLeave()
{
  call SET(false);
  call SetLock(nil);
}

procedure {:intro} {:layer 1} SetLock(v: X)
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
