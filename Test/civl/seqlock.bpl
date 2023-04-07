// RUN: %parallel-boogie /lib:base "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "tid"} Tid;

var {:layer 0,2} lock:Option Tid;
var {:layer 0,2} seq:int;
var {:layer 0,3} x:int;
var {:layer 0,3} y:int;

function {:inline} isEven (x:int) : bool { x mod 2 == 0 }
function {:inline} isOdd (x:int) : bool { x mod 2 != 0 }

// =============================================================================
// Implementation of atomic read and write operations (to variables x and y)
// using a seqlock (comprising variables lock and seq).

action {:layer 3} READ () returns (v:int, w:int)
{
  v := x;
  w := y;
}

action {:layer 3} WRITE (v:int, w:int)
modifies x, y;
{
  x := v;
  y := w;
}

yield procedure {:layer 2} read () returns (v:int, w:int)
refines READ;
{
  var seq1:int;
  var seq2:int;
  while (true)
  invariant {:yields} true;
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

yield procedure {:layer 2}
write ({:hide}{:linear "tid"} tid:Tid, v:int, w:int)
refines WRITE;
preserves call SeqLockInv();
{
  call acquire(tid);
  call locked_inc_seq(tid);
  call locked_write_x(tid, v);
  call locked_write_y(tid, w);
  par SeqLockInv() | HoldLock(tid);
  call locked_inc_seq(tid);
  call release(tid);
}

yield invariant{:layer 2} SeqLockInv ();
invariant lock == None() <==> isEven(seq);

yield invariant{:layer 2} HoldLock ({:linear "tid"} tid:Tid);
invariant lock == Some(tid);

// =============================================================================
// Abstractions of atomic actions with stronger mover types
// Key insights:
// * First read of seq can be stale (i.e., less than the actual value), and
//   reads of x and y only return the correct value in case the previously read
//   value of seq was even and is still the actual value (otherwise any value
//   can be returned).
// * Increments of seq and writes of x and y are lock-protected, and writes only
//   happen when seq is odd.

-> action {:layer 2} STALE_READ_SEQ () returns (r:int)
{
  assume r <= seq;
}

-> action {:layer 2} STALE_READ_X (seq1:int) returns (r:int)
{
  assert seq >= seq1;
  if (isEven(seq) && seq == seq1) {
    r := x;
  }
}

-> action {:layer 2} STALE_READ_Y (seq1:int) returns (r:int)
{
  assert seq >= seq1;
  if (isEven(seq) && seq == seq1) {
    r := y;
  }
}

action {:layer 2} LOCKED_INC_SEQ ({:linear "tid"} tid:Tid)
modifies seq;
{
  assert lock == Some(tid);
  seq := seq + 1;
}

<-> action {:layer 2} LOCKED_WRITE_X ({:linear "tid"} tid:Tid, v:int)
modifies x;
{
  assert isOdd(seq);
  assert lock == Some(tid);
  x := v;
}

<-> action {:layer 2} LOCKED_WRITE_Y ({:linear "tid"} tid:Tid, v:int)
modifies y;
{
  assert isOdd(seq);
  assert lock == Some(tid);
  y := v;
}

yield procedure {:layer 1} stale_read_seq () returns (r:int)
refines STALE_READ_SEQ;
{ call r := read_seq(); }

yield procedure {:layer 1} stale_read_x ({:layer 1} seq1:int) returns (r:int)
refines STALE_READ_X;
{ call r := read_x(); }

yield procedure {:layer 1} stale_read_y ({:layer 1} seq1:int) returns (r:int)
refines STALE_READ_Y;
{ call r := read_y(); }

yield procedure {:layer 1} locked_inc_seq ({:layer 1}{:linear "tid"} tid:Tid)
refines LOCKED_INC_SEQ;
{ call inc_seq(); }

yield procedure {:layer 1} locked_write_x ({:layer 1}{:linear "tid"} tid:Tid, v:int)
refines LOCKED_WRITE_X;
{ call write_x(v); }

yield procedure {:layer 1} locked_write_y ({:layer 1}{:linear "tid"} tid:Tid, v:int)
refines LOCKED_WRITE_Y;
{ call write_y(v); }

// =============================================================================
// Primitie atomic actions
// * read and write of x and y
// * read and increment of seq
// * acquire and release of lock

action {:layer 1} READ_X () returns (r:int)
{
  r := x;
}

action {:layer 1} READ_Y () returns (r:int)
{
  r := y;
}

action {:layer 1} WRITE_X (v:int)
modifies x;
{
  x := v;
}

action {:layer 1} WRITE_Y (v:int)
modifies y;
{
  y := v;
}

action {:layer 1,2} READ_SEQ () returns (r:int)
{
  r := seq;
}

action {:layer 1} INC_SEQ ()
modifies seq;
{
  seq := seq + 1;
}

-> action {:layer 1,2} ACQUIRE ({:linear "tid"} tid:Tid)
modifies lock;
{
  assume lock == None();
  lock := Some(tid);
}

<- action {:layer 1,2} RELEASE ({:linear "tid"} tid:Tid)
modifies lock;
{
  assert lock == Some(tid);
  lock := None();
}

yield procedure {:layer 0} read_x () returns (r:int);
refines READ_X;

yield procedure {:layer 0} read_y () returns (r:int);
refines READ_Y;

yield procedure {:layer 0} write_x (v:int);
refines WRITE_X;

yield procedure {:layer 0} write_y (v:int);
refines WRITE_Y;

yield procedure {:layer 0} read_seq () returns (r:int);
refines READ_SEQ;

yield procedure {:layer 0} inc_seq ();
refines INC_SEQ;

yield procedure {:layer 0} acquire ({:linear "tid"} tid:Tid);
refines ACQUIRE;

yield procedure {:layer 0} release ({:linear "tid"} tid:Tid);
refines RELEASE;
