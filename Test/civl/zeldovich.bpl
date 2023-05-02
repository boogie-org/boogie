// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Tid;
const nil: Tid;

var {:layer 0,1} lock_x: Tid;
var {:layer 0,1} lock_y: Tid;
var {:layer 0,2} x: int;
var {:layer 0,2} y: int;

>-< action {:layer 2} GET_X (tid: Lval Tid) returns (v: int)
{
  v := x;
}

>-< action {:layer 2} SET_BOTH (tid: Lval Tid, v: int, w: int)
modifies x, y;
{
  x := v;
  y := w;
}

yield procedure {:layer 1} get_x (tid: Lval Tid) returns (v: int)
refines GET_X;
requires {:layer 1} tid->val != nil;
{
  call acquire_x(tid);
  call v := read_x(tid);
  call release_x(tid);
}

yield procedure {:layer 1} set_both (tid: Lval Tid, v: int, w: int)
refines SET_BOTH;
requires {:layer 1} tid->val != nil;
{
  call acquire_x(tid);
  call acquire_y(tid);
  call write_x(tid, v);
  call release_x(tid); // early release of lock_x
  call write_y(tid, w);
  call release_y(tid);
}

-> action {:layer 1} ACQUIRE_X (tid: Lval Tid)
modifies lock_x;
{
  assert tid->val != nil;
  assume lock_x == nil;
  lock_x := tid->val;
}

<- action {:layer 1} RELEASE_X (tid: Lval Tid)
modifies lock_x;
{
  assert tid->val != nil && lock_x == tid->val;
  lock_x := nil;
}

-> action {:layer 1} ACQUIRE_Y (tid: Lval Tid)
modifies lock_y;
{
  assert tid->val != nil;
  assume lock_y == nil;
  lock_y := tid->val;
}

<- action {:layer 1} RELEASE_Y (tid: Lval Tid)
modifies lock_y;
{
  assert tid->val != nil && lock_y == tid->val;
  lock_y := nil;
}

<-> action {:layer 1} WRITE_X (tid: Lval Tid, v: int)
modifies x;
{
  assert tid->val != nil && lock_x == tid->val;
  x := v;
}

<-> action {:layer 1} WRITE_Y (tid: Lval Tid, v: int)
modifies y;
{
  assert tid->val != nil && lock_y == tid->val;
  y := v;
}

<-> action {:layer 1} READ_X (tid: Lval Tid) returns (r: int)
{
  assert tid->val != nil && lock_x == tid->val;
  r := x;
}

yield procedure {:layer 0} acquire_x (tid: Lval Tid);
refines ACQUIRE_X;

yield procedure {:layer 0} acquire_y (tid: Lval Tid);
refines ACQUIRE_Y;

yield procedure {:layer 0} release_x (tid: Lval Tid);
refines RELEASE_X;

yield procedure {:layer 0} release_y (tid: Lval Tid);
refines RELEASE_Y;

yield procedure {:layer 0} write_x (tid: Lval Tid, v: int);
refines WRITE_X;

yield procedure {:layer 0} write_y (tid: Lval Tid, v: int);
refines WRITE_Y;

yield procedure {:layer 0} read_x (tid: Lval Tid) returns (r: int);
refines READ_X;
