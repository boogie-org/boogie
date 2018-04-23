// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Tid = int;

const nil:Tid;
var {:layer 0,3} l:Tid;
var {:layer 0,5} x:int;

procedure {:atomic}{:layer 5} Client_atomic ({:linear_in "tid"} tid:Tid)
modifies x;
{
  x := x + 1;
} 

procedure {:yields}{:layer 4}{:refines "Client_atomic"} Client ({:linear_in "tid"} tid:Tid)
requires {:layer 3} tid != nil;
{
  yield;
  async call GetLockAbstract(tid);
  yield;
}

procedure {:left}{:layer 4} GetLockAbstract_atomic({:linear_in "tid"} tid:Tid)
modifies x;
{
  x := x + 1; 
}

procedure {:yields}{:layer 3}{:refines "GetLockAbstract_atomic"} GetLockAbstract({:linear_in "tid"} tid:Tid)
requires {:layer 3} tid != nil;
{
  yield;
  call GetLock(tid);
  yield;
}

procedure {:left}{:layer 3} Callback_atomic ({:linear_in "tid"} tid:Tid)
modifies l,x;
{
  assert tid != nil && l == tid;
  x := x + 1;
  l := nil;
}

procedure {:yields}{:layer 2}{:refines "Callback_atomic"} Callback ({:linear_in "tid"} tid:Tid)
{
  var tmp:int;
  yield;
  call tmp := read_x_lock(tid);
  call write_x_lock(tmp+1, tid);
  async call ReleaseLock(tid);
  yield;
}


// -----------------------------------------------------------------------------

procedure {:atomic}{:layer 2,3} GetLock_atomic ({:linear_in "tid"} tid:Tid)
modifies l;
{
  assert tid != nil;
  assume l == nil;
  l := tid;
  async call Callback(tid);
}

procedure {:left}{:layer 2} ReleaseLock_atomic ({:linear_in "tid"} tid:Tid)
modifies l;
{
  assert tid != nil && l == tid;
  l := nil;
}

procedure {:yields}{:layer 1}{:refines "GetLock_atomic"} GetLock ({:linear_in "tid"} tid:Tid)
{
  var success:bool;
  yield;
  while (true) {
    call success := cas_l(nil, tid);
    if (success) {
      async call Callback(tid);
      yield;
      return;
    }
    yield;
  }
  yield;
}

procedure {:yields}{:layer 1}{:refines "ReleaseLock_atomic"} ReleaseLock ({:linear_in "tid"} tid:Tid)
{
  yield;
  call write_l(nil);
  yield;
}

// -----------------------------------------------------------------------------

procedure {:both}{:layer 2} read_x_lock_atomic ({:linear "tid"} tid:Tid) returns (v:int)
{ assert tid != nil && l == tid; v := x; }

procedure {:both}{:layer 2} write_x_lock_atomic (v:int, {:linear "tid"} tid:Tid)
modifies x;
{ assert tid != nil && l == tid; x := v; }

procedure {:yields}{:layer 1}{:refines "read_x_lock_atomic"} read_x_lock ({:linear "tid"} tid:Tid) returns (v:int)
{ yield; call v := read_x(); yield; }
procedure {:yields}{:layer 1}{:refines "write_x_lock_atomic"} write_x_lock (v:int, {:linear "tid"} tid:Tid)
{ yield; call write_x(v); yield; }

// -----------------------------------------------------------------------------

procedure {:atomic}{:layer 1} read_x_atomic () returns (v:int)
{ v := x; }

procedure {:atomic}{:layer 1} write_x_atomic (v:int)
modifies x;
{ x := v; }

procedure {:yields}{:layer 0}{:refines "read_x_atomic"} read_x () returns (v:int);
procedure {:yields}{:layer 0}{:refines "write_x_atomic"} write_x (v:int);

procedure {:atomic} {:layer 1} cas_l_atomic (oldval:Tid, newval:Tid) returns (success:bool)
modifies l;
{
  if (l == oldval) {
    l := newval;
    success := true;
  } else {
    success := false;
  }
}

procedure {:atomic}{:layer 1} write_l_atomic (v:Tid)
modifies l;
{ l := v; }

procedure {:yields}{:layer 0}{:refines "cas_l_atomic"} cas_l (oldval:Tid, newval:Tid) returns (success:bool);
procedure {:yields}{:layer 0}{:refines "write_l_atomic"} write_l (v:Tid);

// ###########################################################################
// Collectors for linear domains

function {:builtin "MapConst"} MapConstBool (bool) : [Tid]bool;

function {:inline} {:linear "tid"} TidCollector (x:Tid) : [Tid]bool
{ MapConstBool(false)[x := true] }

function {:inline} {:linear "tid"} TidSetCollector (x:[Tid]bool) : [Tid]bool
{ x }
