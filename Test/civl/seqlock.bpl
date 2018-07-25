// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Tid;
const nil:Tid;

var {:layer 0,1} lock:Tid;
var {:layer 0,1} seq:int;
var {:layer 0,2} x:int;
var {:layer 0,2} y:int;

function {:inline 1} isEven (x:int) : bool { x mod 2 == 0 }
function {:inline 1} isOdd (x:int) : bool { x mod 2 != 0 }

procedure {:atomic}{:layer 2} READ () returns (v:int, w:int)
{
  v := x;
  w := y;
}

procedure {:atomic}{:layer 2} WRITE ({:linear "tid"} tid:Tid, v:int, w:int)
modifies x, y;
{
  x := v;
  y := w;
}

procedure {:layer 1}{:inline 1} Snapshot() returns (_x:int, _y:int)
{
   _x := x;
   _y := y;
}

procedure {:layer 1}{:yields}{:refines "READ"} read () returns (v:int, w:int)
{
  var seq1:int;
  var seq2:int;

  var {:layer 1} _x:int;
  var {:layer 1} _y:int;
  
  yield;
  while (true)
  {
    yield;
    call seq1 := read_seq();
    call _x, _y := Snapshot();
    yield;
    assert {:layer 1} seq >= seq1 && ((isEven(seq1) && seq1 == seq) ==> (x == _x && y == _y));
    if (isEven(seq1)) {
      call v := read_x();
      yield; assert {:layer 1} seq >= seq1 && ((isEven(seq1) && seq1 == seq) ==> (x == _x && y == _y && v == x));
      call w := read_y();
      yield; assert {:layer 1} seq >= seq1 && ((isEven(seq1) && seq1 == seq) ==> (x == _x && y == _y && v == x && w == y));
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

procedure {:layer 1}{:yields}{:refines "WRITE"} write ({:linear "tid"} tid:Tid, v:int, w:int)
requires {:layer 1} tid != nil;
requires {:layer 1} lock == nil <==> isEven(seq);
ensures  {:layer 1} lock == nil <==> isEven(seq);
{
  yield;
  assert {:layer 1} tid != nil;
  assert {:layer 1} lock == nil <==> isEven(seq);
  call acquire(tid);
  call inc_seq(tid);
  call write_x(tid, v);
  call write_y(tid, w);
  yield;
  assert {:layer 1} tid != nil && lock == tid;
  assert {:layer 1} lock == nil <==> isEven(seq);
  call inc_seq(tid);
  call release(tid);
  yield;
  assert {:layer 1} lock == nil <==> isEven(seq);
}

procedure {:atomic}{:layer 1} READ_SEQ () returns (r:int)
{
  r := seq;
}

procedure {:atomic}{:layer 1} READ_X () returns (r:int)
{
  if (isEven(seq)) {
    r := x;
  }
}

procedure {:atomic}{:layer 1} READ_Y () returns (r:int)
{
  if (isEven(seq)) {
    r := y;
  }
}

procedure {:right}{:layer 1} ACQUIRE ({:linear "tid"} tid:Tid)
modifies lock;
{
  assert tid != nil;
  assume lock == nil;
  lock := tid;
}

procedure {:left}{:layer 1} RELEASE ({:linear "tid"} tid:Tid)
modifies lock;
{
  assert tid != nil && lock == tid;
  lock := nil;
}

procedure {:atomic}{:layer 1} INC_SEQ ({:linear "tid"} tid:Tid)
modifies seq;
{
  assert tid != nil && lock == tid;
  seq := seq + 1;
}

procedure {:both}{:layer 1} WRITE_X ({:linear "tid"} tid:Tid, v:int)
modifies x;
{
  assert isOdd(seq);
  assert tid != nil && lock == tid;
  x := v;
}

procedure {:both}{:layer 1} WRITE_Y ({:linear "tid"} tid:Tid, v:int)
modifies y;
{
  assert isOdd(seq);
  assert tid != nil && lock == tid;
  y := v;
}

procedure {:yields}{:layer 0}{:refines "READ_SEQ"} read_seq () returns (r:int);
procedure {:yields}{:layer 0}{:refines "READ_X"} read_x () returns (r:int);
procedure {:yields}{:layer 0}{:refines "READ_Y"} read_y () returns (r:int);

procedure {:yields}{:layer 0}{:refines "ACQUIRE"} acquire ({:linear "tid"} tid:Tid);
procedure {:yields}{:layer 0}{:refines "RELEASE"} release ({:linear "tid"} tid:Tid);
procedure {:yields}{:layer 0}{:refines "INC_SEQ"} inc_seq ({:linear "tid"} tid:Tid);
procedure {:yields}{:layer 0}{:refines "WRITE_X"} write_x ({:linear "tid"} tid:Tid, v:int);
procedure {:yields}{:layer 0}{:refines "WRITE_Y"} write_y ({:linear "tid"} tid:Tid, v:int);

function {:builtin "MapConst"} MapConstBool(bool) : [Tid]bool;
function {:inline}{:linear "tid"} TidCollector(tid:Tid) : [Tid]bool
{
  MapConstBool(false)[tid := true]
}
