// RUN: %boogie -noinfer -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type X;
const unique MainTid: X;
const unique Nil: X;

var {:layer 2,5} x: int;
var {:layer 2,3} lock: X;

var {:layer 1,4}{:linear "tid"} unallocated:[X]bool;

procedure {:right} {:layer 2,4} AtomicAllocTid() returns ({:linear "tid"} tid: X)
modifies unallocated;
{ assume tid != Nil && unallocated[tid]; unallocated[tid] := false; }

procedure {:yields} {:layer 1} {:refines "AtomicAllocTid"} AllocTid() returns ({:linear "tid"} tid: X);

procedure {:right} {:layer 3} atomic_acq({:linear "tid"} tid: X)
modifies lock;
{ assert tid != Nil; assume lock == Nil; lock := tid; }

procedure {:yields} {:layer 2} {:refines "atomic_acq"} acq({:linear "tid"} tid: X);

procedure {:left} {:layer 3} atomic_rel({:linear "tid"} tid: X)
modifies lock;
{ assert tid != Nil && lock == tid; lock := Nil; }

procedure {:yields} {:layer 2} {:refines "atomic_rel"} rel({:linear "tid"} tid: X);

procedure {:both} {:layer 3} atomic_read({:linear "tid"} tid: X) returns (v: int)
{ assert tid != Nil && lock == tid; v := x; }

procedure {:yields} {:layer 2} {:refines "atomic_read"} read({:linear "tid"} tid: X) returns (v: int);

procedure {:both} {:layer 3} atomic_write({:linear "tid"} tid: X, v: int)
modifies x;
{ assert tid != Nil && lock == tid; x := v; }

procedure {:yields} {:layer 2} {:refines "atomic_write"} write({:linear "tid"} tid: X, v: int);

procedure {:left} {:layer 4} AtomicIncr({:linear "tid"} tid: X)
modifies x;
{ x := x + 1; }

procedure {:yields} {:layer 3} {:refines "AtomicIncr"} Incr({:linear "tid"} tid: X)
requires {:layer 3} tid != Nil;
{
  var t: int;
  
  yield;
  call acq(tid);
  call t := read(tid);
  call write(tid, t+1);
  call rel(tid);
  yield;
}

procedure {:left} {:layer 5} AtomicIncrBy2()
modifies x;
{ x := x + 2; }

procedure {:yields} {:layer 4} {:refines "AtomicIncrBy2"} IncrBy2()
{
  var {:linear "tid"} tid1: X;
  var {:linear "tid"} tid2: X;
  yield;
  call tid1 := AllocTid();
  call tid2 := AllocTid();
  par Incr(tid1) | Incr(tid2);
  yield;
}

procedure {:yields} {:layer 5} EqualTo2({:linear "tid"} tid: X)
requires {:layer 5} tid == MainTid && x == 0;
{
  yield;
  assert {:layer 5} tid == MainTid && x == 0;
  call IncrBy2();
  yield;
  assert {:layer 5} x == 2;
}

function {:builtin "MapConst"} MapConstBool(bool) : [X]bool;
function {:inline} {:linear "tid"} TidCollector(x: X) : [X]bool
{
  MapConstBool(false)[x := true]
}
function {:inline} {:linear "tid"} TidSetCollector(x: [X]bool) : [X]bool
{
  x
}
