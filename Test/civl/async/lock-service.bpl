// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Tid = int;

const nil:Tid;
var {:layer 0,2} l:Tid;
var {:layer 0,4} x:int;

procedure {:atomic}{:layer 4} Client_atomic ({:linear_in "tid"} tid:Tid)
modifies x;
{
  x := x + 1;
} 

procedure {:yields}{:layer 3}{:refines "Client_atomic"} Client ({:linear_in "tid"} tid:Tid)
requires {:layer 2} tid != nil;
{
  yield;
  async call GetLockAbstract(tid);
  yield;
}

procedure {:left}{:layer 3} GetLockAbstract_atomic({:linear_in "tid"} tid:Tid)
modifies x;
{
  x := x + 1; 
}

procedure {:yields}{:layer 2}{:refines "GetLockAbstract_atomic"} GetLockAbstract({:linear_in "tid"} tid:Tid)
requires {:layer 2} tid != nil;
{
  yield;
  call GetLock(tid);
  yield;
}

procedure {:left}{:layer 2} Callback_atomic ({:linear_in "tid"} tid:Tid)
modifies l,x;
{
  assert tid != nil && l == tid;
  x := x + 1;
  l := nil;
}

procedure {:yields}{:layer 1}{:refines "Callback_atomic"} Callback ({:linear_in "tid"} tid:Tid)
{
  var tmp:int;
  yield;
  call tmp := read_x(tid);
  call write_x(tmp+1, tid);
  async call ReleaseLock(tid);
  yield;
}

// -----------------------------------------------------------------------------

procedure {:atomic}{:layer 1,2} GetLock_atomic ({:linear_in "tid"} tid:Tid)
modifies l;
{
  assert tid != nil;
  assume l == nil;
  l := tid;
  async call Callback(tid);
}

procedure {:left}{:layer 1} ReleaseLock_atomic ({:linear_in "tid"} tid:Tid)
modifies l;
{
  assert tid != nil && l == tid;
  l := nil;
}

procedure {:yields}{:layer 0}{:refines "GetLock_atomic"} GetLock ({:linear_in "tid"} tid:Tid);
procedure {:yields}{:layer 0}{:refines "ReleaseLock_atomic"} ReleaseLock ({:linear_in "tid"} tid:Tid);

// -----------------------------------------------------------------------------

procedure {:both}{:layer 1} read_x_atomic ({:linear "tid"} tid:Tid) returns (v:int)
modifies x;
{ assert tid != nil && l == tid; v := x; }

procedure {:both}{:layer 1} write_x_atomic (v:int, {:linear "tid"} tid:Tid)
modifies x;
{ assert tid != nil && l == tid; x := v; }

procedure {:yields}{:layer 0}{:refines "read_x_atomic"} read_x ({:linear "tid"} tid:Tid) returns (v:int);
procedure {:yields}{:layer 0}{:refines "write_x_atomic"} write_x (v:int, {:linear "tid"} tid:Tid);

// ###########################################################################
// Collectors for linear domains

function {:builtin "MapConst"} MapConstBool (bool) : [Tid]bool;

function {:inline} {:linear "tid"} TidCollector (x:Tid) : [Tid]bool
{ MapConstBool(false)[x := true] }

function {:inline} {:linear "tid"} TidSetCollector (x:[Tid]bool) : [Tid]bool
{ x }
