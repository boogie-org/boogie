// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Tid;
const nil:Tid;

var {:layer 0,2} lock:Tid;
var {:layer 0,2} seq:int;
var {:layer 0,3} x:int;
var {:layer 0,3} y:int;

function {:inline 1} isEven (x:int) : bool { x mod 2 == 0 }
function {:inline 1} isOdd (x:int) : bool { x mod 2 != 0 }

// =============================================================================
// Implementation of atomic read and write operations (to variables x and y)
// using a seqlock (comprising variables lock and seq).

procedure {:atomic}{:layer 3} READ () returns (v:int, w:int)
{
  v := x;
  w := y;
}

procedure {:atomic}{:layer 3} WRITE ({:linear "tid"} tid:Tid, v:int, w:int)
modifies x, y;
{
  x := v;
  y := w;
}

procedure {:layer 2}{:yields}{:refines "READ"} read () returns (v:int, w:int)
{
  var seq1:int;
  var seq2:int;
  yield;
  while (true) {
    yield;
    call seq1 := stale_read_seq();
    if (isEven(seq1)) {
      call v := stale_read_x(seq1);
      call w := stale_read_y(seq1);
      call seq2 := read_seq();
      if (seq1 == seq2) {
        yield;
        return;
      }
    }
    yield;
  }
  yield;
}

procedure {:layer 2}{:yields}{:refines "WRITE"} write ({:linear "tid"} tid:Tid, v:int, w:int)
requires {:layer 2} tid != nil;
requires {:layer 2} lock == nil <==> isEven(seq);
ensures  {:layer 2} lock == nil <==> isEven(seq);
{
  yield;
  assert {:layer 2} tid != nil;
  assert {:layer 2} lock == nil <==> isEven(seq);
  call acquire(tid);
  call locked_inc_seq(tid);
  call locked_write_x(tid, v);
  call locked_write_y(tid, w);
  yield;
  assert {:layer 2} tid != nil && lock == tid;
  assert {:layer 2} lock == nil <==> isEven(seq);
  call locked_inc_seq(tid);
  call release(tid);
  yield;
  assert {:layer 2} lock == nil <==> isEven(seq);
}

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
  assert tid != nil && lock == tid;
  seq := seq + 1;
}

procedure {:both}{:layer 2} LOCKED_WRITE_X ({:linear "tid"} tid:Tid, v:int)
modifies x;
{
  assert isOdd(seq);
  assert tid != nil && lock == tid;
  x := v;
}

procedure {:both}{:layer 2} LOCKED_WRITE_Y ({:linear "tid"} tid:Tid, v:int)
modifies y;
{
  assert isOdd(seq);
  assert tid != nil && lock == tid;
  y := v;
}

procedure {:yields}{:layer 1}{:refines "STALE_READ_SEQ"} stale_read_seq () returns (r:int)
{ yield; call r := read_seq(); yield; }
procedure {:yields}{:layer 1}{:refines "STALE_READ_X"} stale_read_x ({:layer 1} seq1:int) returns (r:int)
{ yield; call r := read_x(); yield; }
procedure {:yields}{:layer 1}{:refines "STALE_READ_Y"} stale_read_y ({:layer 1} seq1:int) returns (r:int)
{ yield; call r := read_y(); yield; }
procedure {:yields}{:layer 1}{:refines "LOCKED_INC_SEQ"} locked_inc_seq ({:layer 1}{:linear "tid"} tid:Tid)
{ yield; call inc_seq(); yield; }
procedure {:yields}{:layer 1}{:refines "LOCKED_WRITE_X"} locked_write_x ({:layer 1}{:linear "tid"} tid:Tid, v:int)
{ yield; call write_x(v); yield; }
procedure {:yields}{:layer 1}{:refines "LOCKED_WRITE_Y"} locked_write_y ({:layer 1}{:linear "tid"} tid:Tid, v:int)
{ yield; call write_y(v); yield; }

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
  assert tid != nil;
  assume lock == nil;
  lock := tid;
}

procedure {:left}{:layer 1,2} RELEASE ({:linear "tid"} tid:Tid)
modifies lock;
{
  assert tid != nil && lock == tid;
  lock := nil;
}

procedure {:yields}{:layer 0}{:refines "READ_X"} read_x () returns (r:int);
procedure {:yields}{:layer 0}{:refines "READ_Y"} read_y () returns (r:int);
procedure {:yields}{:layer 0}{:refines "WRITE_X"} write_x (v:int);
procedure {:yields}{:layer 0}{:refines "WRITE_Y"} write_y (v:int);
procedure {:yields}{:layer 0}{:refines "READ_SEQ"} read_seq () returns (r:int);
procedure {:yields}{:layer 0}{:refines "INC_SEQ"} inc_seq ();
procedure {:yields}{:layer 0}{:refines "ACQUIRE"} acquire ({:linear "tid"} tid:Tid);
procedure {:yields}{:layer 0}{:refines "RELEASE"} release ({:linear "tid"} tid:Tid);

// =============================================================================

function {:builtin "MapConst"} MapConstBool(bool) : [Tid]bool;
function {:inline}{:linear "tid"} TidCollector(tid:Tid) : [Tid]bool
{
  MapConstBool(false)[tid := true]
}
