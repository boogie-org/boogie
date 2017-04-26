// RUN: %boogie -noinfer -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 2,5} x: int;
var {:layer 2,3} lock: X;

procedure {:yields} {:layer 2} AllocTid() returns ({:linear "tid"} tid: X);
ensures {:right} |{L: assume tid != Nil; return true; }|;

procedure {:yields} {:layer 2,3} acq({:linear "tid"} tid: X);
ensures {:right} |{ L: assert tid != Nil; assume lock == Nil; lock := tid; return true; }|;

procedure {:yields} {:layer 2,3} rel({:linear "tid"} tid: X);
ensures {:left} |{ L: assert tid != Nil && lock == tid; lock := Nil; return true; }|;

procedure {:yields} {:layer 2,3} read({:linear "tid"} tid: X) returns (v: int);
ensures {:both} |{ L: assert tid != Nil && lock == tid; v := x; return true; }|;

procedure {:yields} {:layer 2,3} write({:linear "tid"} tid: X, v: int);
ensures {:both} |{ L: assert tid != Nil && lock == tid; x := v; return true; }|;

procedure {:yields} {:layer 3,4} Incr({:linear "tid"} tid: X)
requires {:layer 3} tid != Nil;
ensures {:left} |{ L: x := x + 1; return true; }|;
{
  var t: int;
  
  yield;
  call acq(tid);
  call t := read(tid);
  call write(tid, t+1);
  call rel(tid);
  yield;
}

procedure {:yields} {:layer 4,5} IncrBy2()
ensures {:left} |{ L: x := x + 2; return true; }|;
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

type X;
const unique MainTid: X;
const unique Nil: X;
function {:builtin "MapConst"} MapConstBool(bool) : [X]bool;
function {:inline} {:linear "tid"} TidCollector(x: X) : [X]bool
{
  MapConstBool(false)[x := true]
}

