// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var {:layer 0,2} a:[int]int;
var {:layer 0,1} count: int;
var {:layer 1,2} {:linear "tid"} unallocated:[int]bool;

procedure {:yields} {:layer 2} main()
requires {:layer 1} unallocated == MapConstBool(true);
{
  var {:layer 1} {:linear "tid"} tid:int;
  var i: int;

  yield;
  assert {:layer 1} AllocInv(count, unallocated);
  while (true)
  invariant {:layer 1} AllocInv(count, unallocated);
  {
    call tid, i := Allocate();
    async call P(tid, i);
    yield;
    assert {:layer 1} AllocInv(count, unallocated);
  }
  yield;
}

procedure {:yields} {:layer 2} P({:layer 1} {:linear "tid"} tid: int, i: int)
requires {:layer 1} tid == i;
requires {:layer 1} AllocInv(count, unallocated);
ensures  {:layer 1} AllocInv(count, unallocated);
ensures  {:layer 2} a[tid] == old(a)[tid] + 1;
{
  var t:int;

  yield;
  assert {:layer 1} AllocInv(count, unallocated);
  assert {:layer 2} a[tid] == old(a)[tid];
  call t := Read(tid, i);
  yield;
  assert {:layer 1} AllocInv(count, unallocated);
  assert {:layer 2} a[tid] == t;
  call Write(tid, i, t + 1);
  yield;
  assert {:layer 1} AllocInv(count, unallocated);
  assert {:layer 2} a[tid] == t + 1;
}

procedure {:atomic} {:layer 2,2} AtomicAllocate() returns ({:linear "tid"} tid: int, i: int)
modifies unallocated;
{
  assume unallocated[tid];
  unallocated[tid] := false;
}

procedure {:yields} {:layer 1} {:refines "AtomicAllocate"} Allocate() returns ({:layer 1} {:linear "tid"} tid: int, i: int)
requires {:layer 1} AllocInv(count, unallocated);
ensures  {:layer 1} AllocInv(count, unallocated);
ensures  {:layer 1} tid == i;
{
  yield;
  assert {:layer 1} AllocInv(count, unallocated);
  call i := AllocateLow();
  call tid := MakeLinear(i);
  yield;
  assert {:layer 1} AllocInv(count, unallocated);
}

procedure {:atomic} {:layer 2,2} AtomicRead({:linear "tid"} tid: int, i: int) returns (val: int)
{
  val := a[tid];
}

procedure {:yields} {:layer 1} {:refines "AtomicRead"} Read({:layer 1} {:linear "tid"} tid: int, i: int) returns (val: int)
requires {:layer 1} tid == i;
requires {:layer 1} AllocInv(count, unallocated);
ensures  {:layer 1} AllocInv(count, unallocated);
{
  yield;
  assert {:layer 1} AllocInv(count, unallocated);
  call val := ReadLow(i);
  yield;
  assert {:layer 1} AllocInv(count, unallocated);
}

procedure {:atomic} {:layer 2,2} {:refines "AtomicWrite"} AtomicWrite({:linear "tid"} tid: int, i: int, val: int)
modifies a;
{
  a[tid] := val;
}

procedure {:yields} {:layer 1} {:refines "AtomicWrite"} Write({:layer 1} {:linear "tid"} tid: int, i: int, val: int)
requires {:layer 1} tid == i;
requires {:layer 1} AllocInv(count, unallocated);
ensures  {:layer 1} AllocInv(count, unallocated);
{
  yield;
  assert {:layer 1} AllocInv(count, unallocated);
  call WriteLow(i, val);
  yield;
  assert {:layer 1} AllocInv(count, unallocated);
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
procedure {:layer 1} MakeLinear(i: int) returns ({:linear "tid"} tid: int);
modifies unallocated;
requires unallocated[i];
ensures  tid == i && unallocated == old(unallocated)[i := false];

function {:builtin "MapConst"} MapConstBool(bool): [int]bool;
function {:builtin "MapOr"} MapOr([int]bool, [int]bool) : [int]bool;

function {:inline} {:linear "tid"} TidCollector(x: int) : [int]bool
{
  MapConstBool(false)[x := true]
}
function {:inline} {:linear "tid"} TidSetCollector(x: [int]bool) : [int]bool
{
  x
}

