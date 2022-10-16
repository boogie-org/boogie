// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Tid;
const nil: Tid;

var {:layer 0,1} lock_x: Tid;
var {:layer 0,1} lock_y: Tid;
var {:layer 0,2} x: int;
var {:layer 0,2} y: int;

procedure {:atomic}{:layer 2} GET_X (tid: Lval Tid) returns (v: int)
{
  v := x;
}

procedure {:atomic}{:layer 2} SET_BOTH (tid: Lval Tid, v: int, w: int)
modifies x, y;
{
  x := v;
  y := w;
}

procedure {:layer 1}{:yields}{:refines "GET_X"} get_x (tid: Lval Tid) returns (v: int)
requires {:layer 1} tid->val != nil;
{
  call acquire_x(tid);
  call v := read_x(tid);
  call release_x(tid);
}

procedure {:layer 1}{:yields}{:refines "SET_BOTH"} set_both (tid: Lval Tid, v: int, w: int)
requires {:layer 1} tid->val != nil;
{
  call acquire_x(tid);
  call acquire_y(tid);
  call write_x(tid, v);
  call release_x(tid); // early release of lock_x
  call write_y(tid, w);
  call release_y(tid);
}

procedure {:right}{:layer 1} ACQUIRE_X (tid: Lval Tid)
modifies lock_x;
{
  assert tid->val != nil;
  assume lock_x == nil;
  lock_x := tid->val;
}

procedure {:left}{:layer 1} RELEASE_X (tid: Lval Tid)
modifies lock_x;
{
  assert tid->val != nil && lock_x == tid->val;
  lock_x := nil;
}

procedure {:right}{:layer 1} ACQUIRE_Y (tid: Lval Tid)
modifies lock_y;
{
  assert tid->val != nil;
  assume lock_y == nil;
  lock_y := tid->val;
}

procedure {:left}{:layer 1} RELEASE_Y (tid: Lval Tid)
modifies lock_y;
{
  assert tid->val != nil && lock_y == tid->val;
  lock_y := nil;
}

procedure {:both}{:layer 1} WRITE_X (tid: Lval Tid, v: int)
modifies x;
{
  assert tid->val != nil && lock_x == tid->val;
  x := v;
}

procedure {:both}{:layer 1} WRITE_Y (tid: Lval Tid, v: int)
modifies y;
{
  assert tid->val != nil && lock_y == tid->val;
  y := v;
}

procedure {:both}{:layer 1} READ_X (tid: Lval Tid) returns (r: int)
{
  assert tid->val != nil && lock_x == tid->val;
  r := x;
}

procedure {:yields}{:layer 0}{:refines "ACQUIRE_X"} acquire_x (tid: Lval Tid);
procedure {:yields}{:layer 0}{:refines "ACQUIRE_Y"} acquire_y (tid: Lval Tid);
procedure {:yields}{:layer 0}{:refines "RELEASE_X"} release_x (tid: Lval Tid);
procedure {:yields}{:layer 0}{:refines "RELEASE_Y"} release_y (tid: Lval Tid);
procedure {:yields}{:layer 0}{:refines "WRITE_X"} write_x (tid: Lval Tid, v: int);
procedure {:yields}{:layer 0}{:refines "WRITE_Y"} write_y (tid: Lval Tid, v: int);
procedure {:yields}{:layer 0}{:refines "READ_X"} read_x (tid: Lval Tid) returns (r: int);
