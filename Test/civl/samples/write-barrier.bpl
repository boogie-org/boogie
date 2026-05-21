// RUN: %parallel-boogie "%s" > "%t"
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

yield invariant {:layer 2} YieldColorOnlyGetsDarker(old_Color: int);
preserves Color >= old_Color;

yield procedure {:layer 2} WriteBarrier({:linear} tid: One Tid)
refines AtomicWriteBarrier;
requires call YieldColorOnlyGetsDarker(WHITE());
ensures call YieldColorOnlyGetsDarker(GRAY());
{
  var colorLocal:int;
  call colorLocal := GetColorNoLock();
  call YieldColorOnlyGetsDarker(Color);
  if (WhiteOrLighter(colorLocal)) { call WriteBarrierSlow(tid); }
}

yield procedure {:layer 1} WriteBarrierSlow({:linear} tid: One Tid)
refines AtomicWriteBarrier;
{
  var colorLocal:int;
  call AcquireLock(tid);
  call colorLocal := GetColorLocked(tid);
  if (WhiteOrLighter(colorLocal)) { call SetColorLocked(tid, GRAY()); }
  call ReleaseLock(tid);
}

atomic action {:layer 2,3} AtomicWriteBarrier({:linear} tid: One Tid)
modifies Color;
{
  assert tid->val != nil;
  if (WhiteOrLighter(Color)) {
    Color := GRAY();
  }
}

right action {:layer 1,1} AtomicAcquireLock({:linear} tid: One Tid)
modifies lock;
{
  assert tid->val != nil;
  assume lock == nil;
  lock := tid->val;
}

left action {:layer 1,1} AtomicReleaseLock({:linear} tid: One Tid)
modifies lock;
{
  assert tid->val != nil;
  assert lock == tid->val;
  lock := nil;
}

atomic action {:layer 1,1} AtomicSetColorLocked({:linear} tid: One Tid, newCol:int)
modifies Color;
{
  assert tid->val != nil;
  assert lock == tid->val;
  Color := newCol;
}

both action {:layer 1,1} AtomicGetColorLocked({:linear} tid: One Tid) returns (col:int)
{
  assert tid->val != nil;
  assert lock == tid->val;
  col := Color;
}

atomic action {:layer 1,2} AtomicGetColorNoLock() returns (col:int)
{
  col := Color;
}

yield procedure {:layer 0} AcquireLock({:linear} tid: One Tid);
refines AtomicAcquireLock;

yield procedure {:layer 0} ReleaseLock({:linear} tid: One Tid);
refines AtomicReleaseLock;

yield procedure {:layer 0} SetColorLocked({:linear} tid: One Tid, newCol:int);
refines AtomicSetColorLocked;

yield procedure {:layer 0} GetColorLocked({:linear} tid: One Tid) returns (col:int);
refines AtomicGetColorLocked;

yield procedure {:layer 0} GetColorNoLock() returns (col:int);
refines AtomicGetColorNoLock;
