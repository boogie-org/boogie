// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Tid;
const unique nil: Tid;

var {:layer 0,3} Color:int;
var {:layer 0,1} lock:Tid;

function {:inline} UNALLOC():int { 0 }
function {:inline} WHITE():int   { 1 }
function {:inline} GRAY():int    { 2 }
function {:inline} BLACK():int   { 3 }
function {:inline} Unalloc(i:int) returns(bool) { i <= 0 }
function {:inline} White(i:int)   returns(bool) { i == 1 }
function {:inline} Gray(i:int)    returns(bool) { i == 2 }
function {:inline} Black(i:int)   returns(bool) { i >= 3 }
function {:inline} WhiteOrLighter(i:int) returns(bool) { i <= 1 }

procedure {:yields} {:layer 2} YieldColorOnlyGetsDarker()
ensures {:layer 2} Color >= old(Color);
{
  yield;
  assert {:layer 2} Color >= old(Color);
}

procedure {:yields} {:layer 2} {:refines "AtomicWriteBarrier"} WriteBarrier({:linear "tid"} tid:Tid)
requires {:layer 2} Color >= WHITE();
ensures  {:layer 2} Color >= GRAY();
{
  var colorLocal:int;
  yield;
  assert {:layer 2} Color >= WHITE();
  call colorLocal := GetColorNoLock();
  call YieldColorOnlyGetsDarker();
  if (WhiteOrLighter(colorLocal)) { call WriteBarrierSlow(tid); }
  yield;
  assert {:layer 2} Color >= GRAY();
}

procedure {:yields} {:layer 1} {:refines "AtomicWriteBarrier"} WriteBarrierSlow({:linear "tid"} tid:Tid)
{
  var colorLocal:int;
  yield;
  call AcquireLock(tid);
  call colorLocal := GetColorLocked(tid);
  if (WhiteOrLighter(colorLocal)) { call SetColorLocked(tid, GRAY()); }
  call ReleaseLock(tid);
  yield;
}

procedure {:atomic} {:layer 2,3} AtomicWriteBarrier({:linear "tid"} tid:Tid)
modifies Color;
{
  assert tid != nil;
  if (WhiteOrLighter(Color)) {
    Color := GRAY();
  }
}

procedure {:right} {:layer 1,1} AtomicAcquireLock({:linear "tid"} tid: Tid)
modifies lock;
{
  assert tid != nil;
  assume lock == nil;
  lock := tid; 
}

procedure {:left} {:layer 1,1} AtomicReleaseLock({:linear "tid"} tid: Tid)
modifies lock;
{
  assert tid != nil;
  assert lock == tid;
  lock := nil;
}

procedure {:atomic} {:layer 1,1} AtomicSetColorLocked({:linear "tid"} tid:Tid, newCol:int)
modifies Color;
{
  assert tid != nil;
  assert lock == tid;
  Color := newCol;
}

procedure {:both} {:layer 1,1} AtomicGetColorLocked({:linear "tid"} tid:Tid) returns (col:int)
{
  assert tid != nil;
  assert lock == tid;
  col := Color;
}

procedure {:atomic} {:layer 1,2} AtomicGetColorNoLock() returns (col:int)
{
  col := Color;
}

procedure {:yields} {:layer 0} {:refines "AtomicAcquireLock"} AcquireLock({:linear "tid"} tid: Tid);
procedure {:yields} {:layer 0} {:refines "AtomicReleaseLock"} ReleaseLock({:linear "tid"} tid: Tid);
procedure {:yields} {:layer 0} {:refines "AtomicSetColorLocked"} SetColorLocked({:linear "tid"} tid:Tid, newCol:int);
procedure {:yields} {:layer 0} {:refines "AtomicGetColorLocked"} GetColorLocked({:linear "tid"} tid:Tid) returns (col:int);
procedure {:yields} {:layer 0} {:refines "AtomicGetColorNoLock"} GetColorNoLock() returns (col:int);

function {:builtin "MapConst"} MapConstBool(bool): [Tid]bool;
function {:builtin "MapOr"} MapOr([Tid]bool, [Tid]bool) : [Tid]bool;

function {:inline} {:linear "tid"} TidCollector(x: Tid) : [Tid]bool
{
  MapConstBool(false)[x := true]
}
function {:inline} {:linear "tid"} TidSetCollector(x: [Tid]bool) : [Tid]bool
{
  x
}
