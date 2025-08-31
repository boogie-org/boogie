// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type X;
const MainTid: X;

var {:layer 0,2} x: int;

yield procedure {:layer 0} Incr();
refines AtomicIncr;

left action {:layer 1} AtomicIncr()
modifies x;
{ x := x + 1; }

yield procedure {:layer 1} IncrBy2()
refines AtomicIncrBy2;
{
  call Incr() | Incr();
}

left action {:layer 2} AtomicIncrBy2()
modifies x;
{ x := x + 2; }

yield procedure {:layer 2} EqualTo2({:linear} tid: One X)
requires call YieldPre(tid);
ensures call YieldPost();
{
  call IncrBy2();
}

yield invariant {:layer 2} YieldPre({:linear} tid: One X);
preserves tid->val == MainTid && x == 0;

yield invariant {:layer 2} YieldPost();
preserves x == 2;
