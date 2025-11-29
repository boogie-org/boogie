// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,2} a: [int]int;
var {:layer 0,1} count: int;
var {:layer 1,2} {:linear} unallocated: Set (One int);

yield invariant {:layer 1} Yield1();
preserves AllocInv(count, unallocated);

yield invariant {:layer 2} Yield2({:linear} tid: One int, v: int);
preserves a[tid->val] == v;

yield procedure {:layer 2} main()
requires call Yield1();
{
  var {:layer 1,2} tid: One int;
  var i: int;

  while (true)
  invariant {:yields} true;
  invariant call Yield1();
  {
    call tid, i := Allocate();
    async call P(tid, i);
  }
}

yield procedure {:layer 2} P({:layer 1,2} {:linear} tid: One int, i: int)
requires {:layer 1} tid->val == i;
preserves call Yield1();
requires call Yield2(tid, old(a)[tid->val]);
ensures call Yield2(tid, old(a)[tid->val] + 1);
{
  var t:int;

  call t := Read(tid, i);
  call Yield1() | Yield2(tid, t);
  call Write(tid, i, t + 1);
}

atomic action {:layer 2,2} AtomicAllocate() returns ({:linear} tid: One int, i: int)
modifies unallocated;
{
  assume Set_Contains(unallocated, One(i));
  tid := One(i);
  call One_Get(unallocated, tid);
}

yield procedure {:layer 1}
Allocate() returns ({:layer 1} {:linear} tid: One int, i: int)
refines AtomicAllocate;
ensures {:layer 1} tid->val == i;
preserves call Yield1();
{
  call i := AllocateLow();
  call {:layer 1} tid, unallocated := MakeLinear(i, unallocated);
}

atomic action {:layer 2,2} AtomicRead({:linear} tid: One int, i: int) returns (val: int)
{
  val := a[tid->val];
}

yield procedure {:layer 1}
Read({:layer 1} {:linear} tid: One int, i: int) returns (val: int)
refines AtomicRead;
requires {:layer 1} tid->val == i;
preserves call Yield1();
{
  call val := ReadLow(i);
}

atomic action {:layer 2,2} AtomicWrite({:linear} tid: One int, i: int, val: int)
modifies a;
{
  a[tid->val] := val;
}

yield procedure {:layer 1}
Write({:layer 1} {:linear} tid: One int, i: int, val: int)
refines AtomicWrite;
requires {:layer 1} tid->val == i;
preserves call Yield1();
{
  call WriteLow(i, val);
}

function {:inline} AllocInv(count: int, unallocated: Set (One int)): bool
{
  (forall x: int :: Set_Contains(unallocated, One(x)) || x < count)
}

atomic action {:layer 1,1} AtomicReadLow(i: int) returns (val: int)
{
  val := a[i];
}

atomic action {:layer 1,1} AtomicWriteLow(i: int, val: int)
modifies a;
{
  a[i] := val;
}

atomic action {:layer 1,1} AtomicAllocateLow() returns (i: int)
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

pure action MakeLinear(i: int, {:linear_in} unallocated: Set (One int))
returns ({:linear} tid: One int, {:linear} unallocated': Set (One int))
{
  unallocated' := unallocated;
  tid := One(i);
  call One_Get(unallocated', tid);
}
