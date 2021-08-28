// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "tid"} Tid;
type {:datatype} Option _;
function {:constructor} None<T>() : Option T;
function {:constructor} Some<T>(tid:Tid) : Option T;

var {:layer 0,2} lock:Option Tid;
var {:layer 0,2} seq:int;
var {:layer 0,3} x:int;
var {:layer 0,3} y:int;

function {:inline} isEven (x:int) : bool { x mod 2 == 0 }
function {:inline} isOdd (x:int) : bool { x mod 2 != 0 }

// =============================================================================
// Implementation of atomic read and write operations (to variables x and y)
// using a seqlock (comprising variables lock and seq).

procedure {:atomic}{:layer 3} READ () returns (v:int, w:int)
{
  v := x;
  w := y;
}

procedure {:atomic}{:layer 3} WRITE (v:int, w:int)
modifies x, y;
{
  x := v;
  y := w;
}

procedure {:layer 2}{:yields}{:refines "READ"} read () returns (v:int, w:int)
{
  var seq1:int;
  var seq2:int;
  while (true)
  invariant {:yields}{:layer 1,2} true;
  {
    call seq1 := stale_read_seq();
    if (isEven(seq1)) {
      call v := stale_read_x(seq1);
      call w := stale_read_y(seq1);
      call seq2 := read_seq();
      if (seq1 == seq2) {
        return;
      }
    }
  }
}

procedure {:layer 2}{:yields}{:refines "WRITE"}
{:yield_preserves "SeqLockInv"}
write ({:hide}{:linear "tid"} tid:Tid, v:int, w:int)
{
  call acquire(tid);
  call locked_inc_seq(tid);
  call locked_write_x(tid, v);
  call locked_write_y(tid, w);
  par SeqLockInv() | HoldLock(tid);
  call locked_inc_seq(tid);
  call release(tid);
}

procedure {:yield_invariant}{:layer 2} SeqLockInv ();
requires lock == None() <==> isEven(seq);

procedure {:yield_invariant}{:layer 2} HoldLock ({:linear "tid"} tid:Tid);
requires lock == Some(tid);

// =============================================================================
// Abstractions of atomic actions with stronger mover types
// Key insights:
// * First read of seq can be stale (i.e., less than the actual value), and
//   reads of x and y only return the correct value in case the previously read
//   value of seq was even and is still the actual value (otherwise any value
//   can be returned).
// * Increments of seq and writes of x and y are lock-protected, and writes only
//   happen when seq is odd.

procedure {:right}{:layer 2} STALE_READ_SEQ () returns (r:int)
{
  assume r <= seq;
}

procedure {:right}{:layer 2} STALE_READ_X (seq1:int) returns (r:int)
{
  assert seq >= seq1;
  if (isEven(seq) && seq == seq1) {
    r := x;
  }
}

procedure {:right}{:layer 2} STALE_READ_Y (seq1:int) returns (r:int)
{
  assert seq >= seq1;
  if (isEven(seq) && seq == seq1) {
    r := y;
  }
}

procedure {:atomic}{:layer 2} LOCKED_INC_SEQ ({:linear "tid"} tid:Tid)
modifies seq;
{
  assert lock == Some(tid);
  seq := seq + 1;
}

procedure {:both}{:layer 2} LOCKED_WRITE_X ({:linear "tid"} tid:Tid, v:int)
modifies x;
{
  assert isOdd(seq);
  assert lock == Some(tid);
  x := v;
}

procedure {:both}{:layer 2} LOCKED_WRITE_Y ({:linear "tid"} tid:Tid, v:int)
modifies y;
{
  assert isOdd(seq);
  assert lock == Some(tid);
  y := v;
}

procedure {:yields}{:layer 1}{:refines "STALE_READ_SEQ"} stale_read_seq () returns (r:int)
{ call r := read_seq(); }
procedure {:yields}{:layer 1}{:refines "STALE_READ_X"} stale_read_x ({:layer 1} seq1:int) returns (r:int)
{ call r := read_x(); }
procedure {:yields}{:layer 1}{:refines "STALE_READ_Y"} stale_read_y ({:layer 1} seq1:int) returns (r:int)
{ call r := read_y(); }
procedure {:yields}{:layer 1}{:refines "LOCKED_INC_SEQ"} locked_inc_seq ({:layer 1}{:linear "tid"} tid:Tid)
{ call inc_seq(); }
procedure {:yields}{:layer 1}{:refines "LOCKED_WRITE_X"} locked_write_x ({:layer 1}{:linear "tid"} tid:Tid, v:int)
{ call write_x(v); }
procedure {:yields}{:layer 1}{:refines "LOCKED_WRITE_Y"} locked_write_y ({:layer 1}{:linear "tid"} tid:Tid, v:int)
{ call write_y(v); }

// =============================================================================
// Primitie atomic actions
// * read and write of x and y
// * read and increment of seq
// * acquire and release of lock

procedure {:atomic}{:layer 1} READ_X () returns (r:int)
{
  r := x;
}

procedure {:atomic}{:layer 1} READ_Y () returns (r:int)
{
  r := y;
}

procedure {:atomic}{:layer 1} WRITE_X (v:int)
modifies x;
{
  x := v;
}

procedure {:atomic}{:layer 1} WRITE_Y (v:int)
modifies y;
{
  y := v;
}

procedure {:atomic}{:layer 1,2} READ_SEQ () returns (r:int)
{
  r := seq;
}

procedure {:atomic}{:layer 1} INC_SEQ ()
modifies seq;
{
  seq := seq + 1;
}

procedure {:right}{:layer 1,2} ACQUIRE ({:linear "tid"} tid:Tid)
modifies lock;
{
  assume lock == None();
  lock := Some(tid);
}

procedure {:left}{:layer 1,2} RELEASE ({:linear "tid"} tid:Tid)
modifies lock;
{
  assert lock == Some(tid);
  lock := None();
}

procedure {:yields}{:layer 0}{:refines "READ_X"} read_x () returns (r:int);
procedure {:yields}{:layer 0}{:refines "READ_Y"} read_y () returns (r:int);
procedure {:yields}{:layer 0}{:refines "WRITE_X"} write_x (v:int);
procedure {:yields}{:layer 0}{:refines "WRITE_Y"} write_y (v:int);
procedure {:yields}{:layer 0}{:refines "READ_SEQ"} read_seq () returns (r:int);
procedure {:yields}{:layer 0}{:refines "INC_SEQ"} inc_seq ();
procedure {:yields}{:layer 0}{:refines "ACQUIRE"} acquire ({:linear "tid"} tid:Tid);
procedure {:yields}{:layer 0}{:refines "RELEASE"} release ({:linear "tid"} tid:Tid);
