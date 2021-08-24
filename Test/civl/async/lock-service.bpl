// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:pending_async}{:datatype} PA;
function {:constructor} A_Callback(tid: Tid) : PA;

type {:linear "tid"} Tid = int;

const nil:Tid;
var {:layer 0,4} l:Tid;
var {:layer 0,5} x:int;

procedure {:atomic}{:layer 5} A_Client ()
modifies x;
{
  x := x + 1;
}
procedure {:refines "A_Client"} Client({:hide}{:linear_in "tid"} tid:Tid)
requires {:layer 4} tid != nil;
{
  call GetLockAndCallback(tid);
}

procedure {:atomic}{:layer 4} A_GetLockAndCallback' ({:linear_in "tid"} tid:Tid)
modifies x;
{
  assert tid != nil;
  x := x + 1;
}

procedure {:IS_invariant}{:layer 3} INV({:linear_in "tid"} tid:Tid) returns ({:pending_async "A_Callback"} PAs: [PA]int)
modifies l, x;
{
  assert tid != nil;
  assume l == nil;
  PAs := MapConst(0);
  if (*) {
    l := tid;
    PAs[A_Callback(tid)] := 1;
  } else {
    x := x + 1;
  }
}

procedure {:left}{:layer 3} A_Callback ({:linear_in "tid"} tid:Tid)
modifies l, x;
{
  assert tid != nil && l == tid;
  x := x + 1;
  l := nil;
}
procedure {:yields}{:layer 2}{:refines "A_Callback"} Callback ({:linear_in "tid"} tid:Tid)
{
  var tmp:int;
  call tmp := read_x_lock(tid);
  call write_x_lock(tmp+1, tid);
  async call {:sync} ReleaseLock(tid);
}

procedure {:both}{:layer 2} A_read_x_lock ({:linear "tid"} tid:Tid) returns (v:int)
{ assert tid != nil && l == tid; v := x; }
procedure {:yields}{:layer 1}{:refines "A_read_x_lock"} read_x_lock ({:linear "tid"} tid:Tid) returns (v:int)
{ call v := read_x(); }

procedure {:both}{:layer 2} A_write_x_lock (v:int, {:linear "tid"} tid:Tid)
modifies x;
{ assert tid != nil && l == tid; x := v; }
procedure {:yields}{:layer 1}{:refines "A_write_x_lock"} write_x_lock (v:int, {:linear "tid"} tid:Tid)
{ call write_x(v); }

procedure {:atomic}{:layer 1} A_read_x () returns (v:int)
{ v := x; }
procedure {:yields}{:layer 0}{:refines "A_read_x"} read_x () returns (v:int);

procedure {:atomic}{:layer 1} A_write_x (v:int)
modifies x;
{ x := v; }
procedure {:yields}{:layer 0}{:refines "A_write_x"} write_x (v:int);

// -----------------------------------------------------------------------------

procedure {:atomic}{:layer 3}
{:IS "A_GetLockAndCallback'","INV"}{:elim "A_Callback"}
A_GetLockAndCallback ({:linear_in "tid"} tid:Tid)
returns ({:pending_async "A_Callback"} PAs: [PA]int)
modifies l;
{
  assert tid != nil;
  assume l == nil;
  l := tid;
  PAs := MapConst(0)[A_Callback(tid) := 1];
}
procedure {:yields}{:layer 2}{:refines "A_GetLockAndCallback"} GetLockAndCallback ({:linear_in "tid"} tid:Tid)
{
  call GetLock(tid);
  async call Callback(tid);
}

procedure {:atomic}{:layer 2} A_GetLock ({:linear "tid"} tid:Tid)
modifies l;
{
  assert tid != nil;
  assume l == nil;
  l := tid;
}
procedure {:yields}{:layer 1}{:refines "A_GetLock"} GetLock ({:linear "tid"} tid:Tid)
{
  var success:bool;
  while (true)
  invariant {:yields} {:layer 1} true;
  {
    call success := cas_l(nil, tid);
    if (success) {
      return;
    }
  }
}

procedure {:left}{:layer 2} A_ReleaseLock ({:linear_in "tid"} tid:Tid)
modifies l;
{
  assert tid != nil && l == tid;
  l := nil;
}
procedure {:yields}{:layer 1}{:refines "A_ReleaseLock"} ReleaseLock ({:linear_in "tid"} tid:Tid)
{
  call write_l(nil);
}

procedure {:atomic} {:layer 1} A_cas_l (oldval:Tid, newval:Tid) returns (success:bool)
modifies l;
{
  if (l == oldval) {
    l := newval;
    success := true;
  } else {
    success := false;
  }
}
procedure {:yields}{:layer 0}{:refines "A_cas_l"} cas_l (oldval:Tid, newval:Tid) returns (success:bool);

procedure {:atomic}{:layer 1} A_write_l (v:Tid)
modifies l;
{ l := v; }
procedure {:yields}{:layer 0}{:refines "A_write_l"} write_l (v:Tid);
