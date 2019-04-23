// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Tid;
const nil:Tid;

var {:layer 0,1} lock_x:Tid;
var {:layer 0,1} lock_y:Tid;
var {:layer 0,2} x:int;
var {:layer 0,2} y:int;

procedure {:atomic}{:layer 2} GET_X ({:linear "tid"} tid:Tid) returns (v:int)
{
  v := x;
}

procedure {:atomic}{:layer 2} SET_BOTH ({:linear "tid"} tid:Tid, v:int, w:int)
modifies x, y;
{
  x := v;
  y := w;
}

procedure {:layer 1}{:yields}{:refines "GET_X"} get_x ({:linear "tid"} tid:Tid) returns (v:int)
requires {:layer 1} tid != nil;
{
  yield; assert {:layer 1} tid != nil;
  call acquire_x(tid);
  call v := read_x(tid);
  call release_x(tid);
  yield;
}

procedure {:layer 1}{:yields}{:refines "SET_BOTH"} set_both ({:linear "tid"} tid:Tid, v:int, w:int)
requires {:layer 1} tid != nil;
{
  yield; assert {:layer 1} tid != nil;
  call acquire_x(tid);
  call acquire_y(tid);
  call write_x(tid, v);
  call release_x(tid); // early release of lock_x
  call write_y(tid, w);
  call release_y(tid);
  yield;
}

procedure {:right}{:layer 1} ACQUIRE_X ({:linear "tid"} tid:Tid)
modifies lock_x;
{
  assert tid != nil;
  assume lock_x == nil;
  lock_x := tid;
}

procedure {:left}{:layer 1} RELEASE_X ({:linear "tid"} tid:Tid)
modifies lock_x;
{
  assert tid != nil && lock_x == tid;
  lock_x := nil;
}

procedure {:right}{:layer 1} ACQUIRE_Y ({:linear "tid"} tid:Tid)
modifies lock_y;
{
  assert tid != nil;
  assume lock_y == nil;
  lock_y := tid;
}

procedure {:left}{:layer 1} RELEASE_Y ({:linear "tid"} tid:Tid)
modifies lock_y;
{
  assert tid != nil && lock_y == tid;
  lock_y := nil;
}

procedure {:both}{:layer 1} WRITE_X ({:linear "tid"} tid:Tid, v:int)
modifies x;
{
  assert tid != nil && lock_x == tid;
  x := v;
}

procedure {:both}{:layer 1} WRITE_Y ({:linear "tid"} tid:Tid, v:int)
modifies y;
{
  assert tid != nil && lock_y == tid;
  y := v;
}

procedure {:both}{:layer 1} READ_X ({:linear "tid"} tid:Tid) returns (r:int)
{
  assert tid != nil && lock_x == tid;
  r := x;
}

procedure {:yields}{:layer 0}{:refines "ACQUIRE_X"} acquire_x ({:linear "tid"} tid:Tid);
procedure {:yields}{:layer 0}{:refines "ACQUIRE_Y"} acquire_y ({:linear "tid"} tid:Tid);
procedure {:yields}{:layer 0}{:refines "RELEASE_X"} release_x ({:linear "tid"} tid:Tid);
procedure {:yields}{:layer 0}{:refines "RELEASE_Y"} release_y ({:linear "tid"} tid:Tid);
procedure {:yields}{:layer 0}{:refines "WRITE_X"} write_x ({:linear "tid"} tid:Tid, v:int);
procedure {:yields}{:layer 0}{:refines "WRITE_Y"} write_y ({:linear "tid"} tid:Tid, v:int);
procedure {:yields}{:layer 0}{:refines "READ_X"} read_x ({:linear "tid"} tid:Tid) returns (r:int);

function {:builtin "MapConst"} MapConstBool(bool) : [Tid]bool;
function {:inline}{:linear "tid"} TidCollector(tid:Tid) : [Tid]bool
{
  MapConstBool(false)[tid := true]
}
