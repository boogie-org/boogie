// RUN: %boogie -noinfer -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,2} x: int;

procedure {:yields} {:layer 0,1} Incr();
ensures {:left} |{ L: x := x + 1; return true; }|;

procedure {:yields} {:layer 1,2} IncrBy2()
ensures {:left} |{ L: x := x + 2; return true; }|;
{
  yield;
  par Incr() | Incr();
  yield;
}

procedure {:yields} {:layer 2} EqualTo2({:linear "tid"} tid: X)
requires {:layer 2} tid == MainTid && x == 0;
{
  yield;
  assert {:layer 2} tid == MainTid && x == 0;
  call IncrBy2();
  yield;
  assert {:layer 2} x == 2;
}

type X;
const MainTid: X;
function {:builtin "MapConst"} MapConstBool(bool) : [X]bool;
function {:inline} {:linear "tid"} TidCollector(x: X) : [X]bool
{
  MapConstBool(false)[x := true]
}

