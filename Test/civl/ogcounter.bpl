// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "tid"} X;
const MainTid: X;

var {:layer 0,2} x: int;

procedure {:yields} {:layer 0} {:refines "AtomicIncr"} Incr();

procedure {:left} {:layer 1} AtomicIncr()
modifies x;
{ x := x + 1; }

procedure {:yields} {:layer 1} {:refines "AtomicIncrBy2"} IncrBy2()
{
  par Incr() | Incr();
}

procedure {:left} {:layer 2} AtomicIncrBy2()
modifies x;
{ x := x + 2; }

procedure {:yields} {:layer 2}
{:yield_requires "YieldPre", tid} {:yield_ensures "YieldPost"}
EqualTo2({:linear "tid"} tid: X)
{
  call IncrBy2();
}

yield invariant {:layer 2} YieldPre({:linear "tid"} tid: X);
invariant tid == MainTid && x == 0;

yield invariant {:layer 2} YieldPost();
invariant x == 2;
