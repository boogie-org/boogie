// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "tid"} X;
const unique MainTid: X;
const unique Nil: X;

var {:layer 2,5} x: int;
var {:layer 2,3} lock: X;

var {:layer 1,4}{:linear "tid"} unallocated:[X]bool;

-> action {:layer 2,4} AtomicAllocTid() returns ({:linear "tid"} tid: X)
modifies unallocated;
{ assume tid != Nil && unallocated[tid]; unallocated[tid] := false; }

yield procedure {:layer 1} AllocTid() returns ({:linear "tid"} tid: X);
refines AtomicAllocTid;

-> action {:layer 3} atomic_acq({:linear "tid"} tid: X)
modifies lock;
{ assert tid != Nil; assume lock == Nil; lock := tid; }

yield procedure {:layer 2} acq({:linear "tid"} tid: X);
refines atomic_acq;

<- action {:layer 3} atomic_rel({:linear "tid"} tid: X)
modifies lock;
{ assert tid != Nil && lock == tid; lock := Nil; }

yield procedure {:layer 2} rel({:linear "tid"} tid: X);
refines atomic_rel;

<-> action {:layer 3} atomic_read({:linear "tid"} tid: X) returns (v: int)
{ assert tid != Nil && lock == tid; v := x; }

yield procedure {:layer 2} read({:linear "tid"} tid: X) returns (v: int);
refines atomic_read;

<-> action {:layer 3} atomic_write({:linear "tid"} tid: X, v: int)
modifies x;
{ assert tid != Nil && lock == tid; x := v; }

yield procedure {:layer 2} write({:linear "tid"} tid: X, v: int);
refines atomic_write;

<- action {:layer 4} AtomicIncr({:linear "tid"} tid: X)
modifies x;
{ x := x + 1; }

yield procedure {:layer 3} Incr({:linear "tid"} tid: X)
refines AtomicIncr;
requires {:layer 3} tid != Nil;
{
  var t: int;

  call acq(tid);
  call t := read(tid);
  call write(tid, t+1);
  call rel(tid);
}

<- action {:layer 5} AtomicIncrBy2()
modifies x;
{ x := x + 2; }

yield procedure {:layer 4} IncrBy2()
refines AtomicIncrBy2;
{
  var {:linear "tid"} tid1: X;
  var {:linear "tid"} tid2: X;

  call tid1 := AllocTid();
  call tid2 := AllocTid();
  par Incr(tid1) | Incr(tid2);
}

yield procedure {:layer 5} EqualTo2({:linear "tid"} tid: X)
requires call YieldPre(tid);
ensures call YieldPost();
{
  call IncrBy2();
}

yield invariant {:layer 5} YieldPre({:linear "tid"} tid: X);
invariant tid == MainTid && x == 0;

yield invariant {:layer 5} YieldPost();
invariant x == 2;
