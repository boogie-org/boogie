// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "tid"} Tid = int;

const nil:Tid;
var {:layer 0,4} l:Tid;
var {:layer 0,5} x:int;

action {:layer 5} A_Client ()
modifies x;
{
  x := x + 1;
}
yield procedure {:layer 4} Client({:hide}{:linear_in "tid"} tid:Tid)
refines A_Client;
requires {:layer 4} tid != nil;
{
  call GetLockAndCallback(tid);
}

action {:layer 4} A_GetLockAndCallback' ({:linear_in "tid"} tid:Tid)
modifies x;
{
  assert tid != nil;
  x := x + 1;
}

invariant action {:layer 3} INV({:linear_in "tid"} tid:Tid)
creates A_Callback;
modifies l, x;
{
  assert tid != nil;
  assume l == nil;
  if (*) {
    l := tid;
    call create_async(A_Callback(tid));
  } else {
    x := x + 1;
  }
}

async <- action {:layer 3} A_Callback ({:linear_in "tid"} tid:Tid)
modifies l, x;
{
  assert tid != nil && l == tid;
  x := x + 1;
  l := nil;
}
yield procedure {:layer 2} Callback ({:linear_in "tid"} tid:Tid)
refines A_Callback;
{
  var tmp:int;
  call tmp := read_x_lock(tid);
  call write_x_lock(tmp+1, tid);
  async call {:sync} ReleaseLock(tid);
}

<-> action {:layer 2} A_read_x_lock ({:linear "tid"} tid:Tid) returns (v:int)
{ assert tid != nil && l == tid; v := x; }
yield procedure {:layer 1} read_x_lock ({:linear "tid"} tid:Tid) returns (v:int)
refines A_read_x_lock;
{ call v := read_x(); }

<-> action {:layer 2} A_write_x_lock (v:int, {:linear "tid"} tid:Tid)
modifies x;
{ assert tid != nil && l == tid; x := v; }
yield procedure {:layer 1} write_x_lock (v:int, {:linear "tid"} tid:Tid)
refines A_write_x_lock;
{ call write_x(v); }

action {:layer 1} A_read_x () returns (v:int)
{ v := x; }
yield procedure {:layer 0} read_x () returns (v:int);
refines A_read_x;

action {:layer 1} A_write_x (v:int)
modifies x;
{ x := v; }
yield procedure {:layer 0} write_x (v:int);
refines A_write_x;

// -----------------------------------------------------------------------------

action {:layer 3}
A_GetLockAndCallback ({:linear_in "tid"} tid:Tid)
refines A_GetLockAndCallback' using INV;
creates A_Callback;
modifies l;
{
  assert tid != nil;
  assume l == nil;
  l := tid;
  call create_async(A_Callback(tid));
}
yield procedure {:layer 2} GetLockAndCallback ({:linear_in "tid"} tid:Tid)
refines A_GetLockAndCallback;
{
  call GetLock(tid);
  async call Callback(tid);
}

action {:layer 2} A_GetLock ({:linear "tid"} tid:Tid)
modifies l;
{
  assert tid != nil;
  assume l == nil;
  l := tid;
}
yield procedure {:layer 1} GetLock ({:linear "tid"} tid:Tid)
refines A_GetLock;
{
  var success:bool;
  while (true)
  invariant {:yields} true;
  {
    call success := cas_l(nil, tid);
    if (success) {
      return;
    }
  }
}

<- action {:layer 2} A_ReleaseLock ({:linear_in "tid"} tid:Tid)
modifies l;
{
  assert tid != nil && l == tid;
  l := nil;
}
yield procedure {:layer 1} ReleaseLock ({:linear_in "tid"} tid:Tid)
refines A_ReleaseLock;
{
  call write_l(nil);
}

action {:layer 1} A_cas_l (oldval:Tid, newval:Tid) returns (success:bool)
modifies l;
{
  if (l == oldval) {
    l := newval;
    success := true;
  } else {
    success := false;
  }
}
yield procedure {:layer 0} cas_l (oldval:Tid, newval:Tid) returns (success:bool);
refines A_cas_l;

action {:layer 1} A_write_l (v:Tid)
modifies l;
{ l := v; }
yield procedure {:layer 0} write_l (v:Tid);
refines A_write_l;
