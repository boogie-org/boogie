// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type X;
const unique MainTid: X;
const unique Nil: X;

var {:layer 2,5} x: int;
var {:layer 2,3} lock: X;

var {:layer 1,4}{:linear} unallocated: Set (One X);

right action {:layer 2,4} AtomicAllocTid() returns ({:linear} tid: One X)
modifies unallocated;
{ assume tid->val != Nil && Set_Contains(unallocated, tid); call One_Get(unallocated, tid); }

yield procedure {:layer 1} AllocTid() returns ({:linear} tid: One X);
refines AtomicAllocTid;

right action {:layer 3} atomic_acq({:linear} tid: One X)
modifies lock;
{ assert tid->val != Nil; assume lock == Nil; lock := tid->val; }

yield procedure {:layer 2} acq({:linear} tid: One X);
refines atomic_acq;

left action {:layer 3} atomic_rel({:linear} tid: One X)
modifies lock;
{ assert tid->val != Nil && lock == tid->val; lock := Nil; }

yield procedure {:layer 2} rel({:linear} tid: One X);
refines atomic_rel;

both action {:layer 3} atomic_read({:linear} tid: One X) returns (v: int)
{ assert tid->val != Nil && lock == tid->val; v := x; }

yield procedure {:layer 2} read({:linear} tid: One X) returns (v: int);
refines atomic_read;

both action {:layer 3} atomic_write({:linear} tid: One X, v: int)
modifies x;
{ assert tid->val != Nil && lock == tid->val; x := v; }

yield procedure {:layer 2} write({:linear} tid: One X, v: int);
refines atomic_write;

left action {:layer 4} AtomicIncr({:linear} tid: One X)
modifies x;
{ x := x + 1; }

yield procedure {:layer 3} Incr({:linear} tid: One X)
refines AtomicIncr;
requires {:layer 3} tid->val != Nil;
{
  var t: int;

  call acq(tid);
  call t := read(tid);
  call write(tid, t+1);
  call rel(tid);
}

left action {:layer 5} AtomicIncrBy2()
modifies x;
{ x := x + 2; }

yield procedure {:layer 4} IncrBy2()
refines AtomicIncrBy2;
{
  var {:linear} tid1: One X;
  var {:linear} tid2: One X;

  call tid1 := AllocTid();
  call tid2 := AllocTid();
  call Incr(tid1) | Incr(tid2);
}

yield procedure {:layer 5} EqualTo2({:linear} tid: One X)
requires call YieldPre(tid);
ensures call YieldPost();
{
  call IncrBy2();
}

yield invariant {:layer 5} YieldPre({:linear} tid: One X);
preserves tid->val == MainTid && x == 0;

yield invariant {:layer 5} YieldPost();
preserves x == 2;
