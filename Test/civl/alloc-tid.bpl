// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "tid"} Tid = int;

var {:layer 0,2} a:[int]int;
var {:layer 0,1} count: int;
var {:layer 1,2} {:linear "tid"} unallocated:[int]bool;

yield invariant {:layer 1} Yield1();
invariant AllocInv(count, unallocated);

yield invariant {:layer 2} Yield2({:linear "tid"} tid: int, v: int);
invariant a[tid] == v;

yield procedure {:layer 2} main()
requires call Yield1();
{
  var {:layer 1,2} {:linear "tid"} tid:int;
  var i: int;

  while (true)
  invariant {:yields} true;
  invariant call Yield1();
  {
    call tid, i := Allocate();
    async call P(tid, i);
  }
}

yield procedure {:layer 2} P({:layer 1,2} {:linear "tid"} tid: int, i: int)
requires {:layer 1} tid == i;
preserves call Yield1();
requires call Yield2(tid, old(a)[tid]);
ensures call Yield2(tid, old(a)[tid] + 1);
{
  var t:int;

  call t := Read(tid, i);
  par Yield1() | Yield2(tid, t);
  call Write(tid, i, t + 1);
}

>-< action {:layer 2,2} AtomicAllocate() returns ({:linear "tid"} tid: int, i: int)
modifies unallocated;
{
  assume unallocated[tid];
  unallocated[tid] := false;
}

yield procedure {:layer 1}
Allocate() returns ({:layer 1} {:linear "tid"} tid: int, i: int)
refines AtomicAllocate;
ensures {:layer 1} tid == i;
preserves call Yield1();
{
  call i := AllocateLow();
  call tid := MakeLinear(i);
}

>-< action {:layer 2,2} AtomicRead({:linear "tid"} tid: int, i: int) returns (val: int)
{
  val := a[tid];
}

yield procedure {:layer 1}
Read({:layer 1} {:linear "tid"} tid: int, i: int) returns (val: int)
refines AtomicRead;
requires {:layer 1} tid == i;
preserves call Yield1();
{
  call val := ReadLow(i);
}

>-< action {:layer 2,2} AtomicWrite({:linear "tid"} tid: int, i: int, val: int)
modifies a;
{
  a[tid] := val;
}

yield procedure {:layer 1}
Write({:layer 1} {:linear "tid"} tid: int, i: int, val: int)
refines AtomicWrite;
requires {:layer 1} tid == i;
preserves call Yield1();
{
  call WriteLow(i, val);
}

function {:inline} AllocInv(count: int, unallocated:[int]bool): (bool)
{
  (forall x: int :: unallocated[x] || x < count)
}

>-< action {:layer 1,1} AtomicReadLow(i: int) returns (val: int)
{
  val := a[i];
}

>-< action {:layer 1,1} AtomicWriteLow(i: int, val: int)
modifies a;
{
  a[i] := val;
}

>-< action {:layer 1,1} AtomicAllocateLow() returns (i: int)
modifies count;
{
  i := count;
  count := i + 1;
}

yield procedure {:layer 0} ReadLow(i: int) returns (val: int);
refines AtomicReadLow;

yield procedure {:layer 0} WriteLow(i: int, val: int);
refines AtomicWriteLow;

yield procedure {:layer 0} AllocateLow() returns (i: int);
refines AtomicAllocateLow;

// We can prove that this primitive procedure preserves the permission invariant locally.
// We only need to use its specification and the definitions of TidCollector and TidSetCollector.
action {:layer 1} MakeLinear(i: int) returns ({:linear "tid"} tid: int)
modifies unallocated;
{
  assert unallocated[i];
  tid := i;
  unallocated := unallocated[i := false];
}
