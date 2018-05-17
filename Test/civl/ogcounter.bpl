// RUN: %boogie -noinfer -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type X;
const MainTid: X;

var {:layer 0,2} x: int;

procedure {:yields} {:layer 0} {:refines "AtomicIncr"} Incr();

procedure {:left} {:layer 1} AtomicIncr()
modifies x;
{ x := x + 1; }

procedure {:yields} {:layer 1} {:refines "AtomicIncrBy2"} IncrBy2()
{
  yield;
  par Incr() | Incr();
  yield;
}

procedure {:left} {:layer 2} AtomicIncrBy2()
modifies x;
{ x := x + 2; }

procedure {:yields} {:layer 2} EqualTo2({:linear "tid"} tid: X)
requires {:layer 2} tid == MainTid && x == 0;
{
  yield;
  assert {:layer 2} tid == MainTid && x == 0;
  call IncrBy2();
  yield;
  assert {:layer 2} x == 2;
}

function {:builtin "MapConst"} MapConstBool(bool) : [X]bool;
function {:inline} {:linear "tid"} TidCollector(x: X) : [X]bool
{
  MapConstBool(false)[x := true]
}

