// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "tid"} Tid = int;

var {:layer 0,2} a:[int]int;
var {:layer 0,1} count: int;
var {:layer 1,2} {:linear "tid"} unallocated:[int]bool;

procedure {:yield_invariant} {:layer 1} Yield1();
requires AllocInv(count, unallocated);

procedure {:yield_invariant} {:layer 2} Yield2({:linear "tid"} tid: int, v: int);
requires a[tid] == v;

procedure {:yields} {:layer 2}
{:yield_requires "Yield1"}
main()
{
  var {:layer 1,2} {:linear "tid"} tid:int;
  var i: int;

  while (true)
  invariant {:yields} {:layer 1,2} {:yield_loop "Yield1"} true;
  {
    call tid, i := Allocate();
    async call P(tid, i);
  }
}

procedure {:yields} {:layer 2}
{:yield_preserves "Yield1"}
{:yield_requires "Yield2", tid, old(a)[tid]}
{:yield_ensures  "Yield2", tid, old(a)[tid] + 1}
P({:layer 1,2} {:linear "tid"} tid: int, i: int)
requires {:layer 1} tid == i;
{
  var t:int;

  call t := Read(tid, i);
  par Yield1() | Yield2(tid, t);
  call Write(tid, i, t + 1);
}

procedure {:atomic} {:layer 2,2} AtomicAllocate() returns ({:linear "tid"} tid: int, i: int)
modifies unallocated;
{
  assume unallocated[tid];
  unallocated[tid] := false;
}

procedure {:yields} {:layer 1} {:refines "AtomicAllocate"}
{:yield_preserves "Yield1"}
Allocate() returns ({:layer 1} {:linear "tid"} tid: int, i: int)
ensures {:layer 1} tid == i;
{
  call i := AllocateLow();
  call tid := MakeLinear(i);
}

procedure {:atomic} {:layer 2,2} AtomicRead({:linear "tid"} tid: int, i: int) returns (val: int)
{
  val := a[tid];
}

procedure {:yields} {:layer 1} {:refines "AtomicRead"}
{:yield_preserves "Yield1"}
Read({:layer 1} {:linear "tid"} tid: int, i: int) returns (val: int)
requires {:layer 1} tid == i;
{
  call val := ReadLow(i);
}

procedure {:atomic} {:layer 2,2} AtomicWrite({:linear "tid"} tid: int, i: int, val: int)
modifies a;
{
  a[tid] := val;
}

procedure {:yields} {:layer 1} {:refines "AtomicWrite"}
{:yield_preserves "Yield1"}
Write({:layer 1} {:linear "tid"} tid: int, i: int, val: int)
requires {:layer 1} tid == i;
{
  call WriteLow(i, val);
}

function {:inline} AllocInv(count: int, unallocated:[int]bool): (bool)
{
  (forall x: int :: unallocated[x] || x < count)
}

procedure {:atomic} {:layer 1,1} AtomicReadLow(i: int) returns (val: int)
{
  val := a[i];
}

procedure {:atomic} {:layer 1,1} AtomicWriteLow(i: int, val: int)
modifies a;
{
  a[i] := val;
}

procedure {:atomic} {:layer 1,1} AtomicAllocateLow() returns (i: int)
modifies count;
{
  i := count;
  count := i + 1;
}

procedure {:yields} {:layer 0} {:refines "AtomicReadLow"} ReadLow(i: int) returns (val: int);
procedure {:yields} {:layer 0} {:refines "AtomicWriteLow"} WriteLow(i: int, val: int);
procedure {:yields} {:layer 0} {:refines "AtomicAllocateLow"} AllocateLow() returns (i: int);

// We can prove that this primitive procedure preserves the permission invariant locally.
// We only need to use its specification and the definitions of TidCollector and TidSetCollector.
procedure {:intro} {:layer 1} MakeLinear(i: int) returns ({:linear "tid"} tid: int)
modifies unallocated;
{
  assert unallocated[i];
  tid := i;
  unallocated := unallocated[i := false];
}
