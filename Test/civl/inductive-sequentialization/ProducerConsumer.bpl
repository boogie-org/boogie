// RUN: %boogie -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,3} C:[int]int; // FIFO channel
var {:layer 0,3} head:int;   // head index of the channel
var {:layer 0,3} tail:int;   // tail index of the channel

const unique prod_id:int;
const unique cons_id:int;

type {:pending_async}{:datatype} PA;
function {:pending_async "PRODUCER"}{:constructor} PRODUCER_PA(x:int, pid:int) : PA;
function {:pending_async "CONSUMER"}{:constructor} CONSUMER_PA(x:int, pid:int) : PA;

function {:inline} NoPAs () : [PA]int
{ (lambda pa:PA :: 0) }

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}
{:IS "MAIN'","INV"}{:elim "PRODUCER"}{:elim "CONSUMER","CONSUMER'"}
MAIN ({:linear_in "pid"} prod_pid:int, {:linear_in "pid"} cons_pid:int)
returns ({:pending_async "PRODUCER","CONSUMER"} PAs:[PA]int)
{
  assert prod_pid == prod_id;
  assert cons_pid == cons_id;
  assert head == tail;
  PAs := NoPAs()[PRODUCER_PA(1, prod_pid) := 1][CONSUMER_PA(1, cons_pid) := 1];
}

procedure {:atomic}{:layer 3}
MAIN' ({:linear_in "pid"} prod_pid:int, {:linear_in "pid"} cons_pid:int)
modifies C, head, tail;
{
  assert prod_pid == prod_id;
  assert cons_pid == cons_id;
  assert head == tail;
  havoc C, head, tail;
  assume head == tail;
}

procedure {:IS_invariant}{:layer 2}
INV ({:linear_in "pid"} prod_pid:int, {:linear_in "pid"} cons_pid:int)
returns ({:pending_async "PRODUCER","CONSUMER"} PAs:[PA]int, {:choice} choice:PA)
modifies C, head, tail;
{
  assert prod_pid == prod_id;
  assert cons_pid == cons_id;
  assert head == tail;

  havoc C, head, tail;

  assume
  (exists c:int ::  c > 0 &&
    (
      (head == tail &&
       PAs == NoPAs()[PRODUCER_PA(c, prod_pid) := 1][CONSUMER_PA(c, cons_pid) := 1] &&
       choice == PRODUCER_PA(c, prod_pid))
      ||
      (tail == head + 1 && C[head] == 0 &&
       PAs == NoPAs()[CONSUMER_PA(c, cons_pid) := 1] &&
       choice == CONSUMER_PA(c, cons_pid))
      ||
      (tail == head + 1 && C[head] == c &&
       PAs == NoPAs()[PRODUCER_PA(c+1, prod_pid) := 1][CONSUMER_PA(c, cons_pid) := 1] &&
       choice == CONSUMER_PA(c, cons_pid))
      ||
      (head == tail &&
       PAs == NoPAs())
    )
  );
}

////////////////////////////////////////////////////////////////////////////////

procedure {:left}{:layer 2}
PRODUCER (x:int, {:linear_in "pid"} pid:int)
returns ({:pending_async "PRODUCER"} PAs:[PA]int)
modifies C, tail;
{
  assert pid == prod_id;

  if (*)
  {
    C[tail] := x;
    tail := tail + 1;
    PAs := NoPAs()[PRODUCER_PA(x+1, pid) := 1];
  }
  else
  {
    C[tail] := 0;
    tail := tail + 1;
    PAs := NoPAs();
  }
}

procedure {:atomic}{:layer 2}
CONSUMER (x:int, {:linear_in "pid"} pid:int)
returns ({:pending_async "CONSUMER"} PAs:[PA]int)
modifies head;
{
  var x':int;

  assert pid == cons_id;
  assert head < tail ==> C[head] == x || C[head] == 0;  // assertion to discharge

  assume head < tail;
  x' := C[head];
  head := head + 1;
  if (x' != 0)
  {
    PAs := NoPAs()[CONSUMER_PA(x'+1, pid) := 1];
  }
  else
  {
    PAs := NoPAs();
  }
}

////////////////////////////////////////////////////////////////////////////////

procedure {:IS_abstraction}{:layer 2}
CONSUMER' (x:int, {:linear_in "pid"} pid:int)
returns ({:pending_async "CONSUMER"} PAs:[PA]int)
modifies head;
{
  var x':int;

  assert pid == cons_id;
  assert head < tail && (C[head] == x || C[head] == 0);

  assume head < tail;
  x' := C[head];
  head := head + 1;
  if (x' != 0)
  {
    PAs := NoPAs()[CONSUMER_PA(x'+1, pid) := 1];
  }
  else
  {
    PAs := NoPAs();
  }
}

////////////////////////////////////////////////////////////////////////////////

procedure {:yields}{:layer 1}{:refines "MAIN"}
main ({:linear_in "pid"} prod_pid:int, {:linear_in "pid"} cons_pid:int)
{
  async call producer(1, prod_pid);
  async call consumer(1, cons_pid);
}

procedure {:yields}{:layer 1}{:refines "PRODUCER"}
producer (x:int, {:linear_in "pid"} pid:int)
{
  if (*)
  {
    call send(x);
    async call producer(x+1, pid);
  }
  else
  {
    call send(0);
  }
}

procedure {:yields}{:layer 1}{:refines "CONSUMER"}
consumer (y:int, {:linear_in "pid"} pid:int)
{
  var y':int;

  call y' := receive();
  if (y' != 0)
  {
    call assert_eq(y', y); // low-level assertion to discharge
    async call consumer(y'+1, pid);
  }
}

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 1} SEND (m:int)
modifies C, tail;
{
  C[tail] := m;
  tail := tail + 1;
}

procedure {:atomic}{:layer 1} RECEIVE () returns (m:int)
modifies C, head;
{
  assume head < tail;
  m := C[head];
  head := head + 1;
}

procedure {:both}{:layer 1} ASSERT_EQ (a:int, b:int)
{
  assert a == b;
}

procedure {:yields}{:layer 0}{:refines "SEND"} send (m:int);
procedure {:yields}{:layer 0}{:refines "RECEIVE"} receive () returns (m:int);
procedure {:yields}{:layer 0}{:refines "ASSERT_EQ"} assert_eq (a:int, b:int);

////////////////////////////////////////////////////////////////////////////////

function {:builtin "MapConst"} MapConstBool (bool) : [int]bool;
function {:builtin "MapOr"} MapOr ([int]bool, [int]bool) : [int]bool;

function {:inline}{:linear "pid"} PidCollector (pid:int) : [int]bool
{
  MapConstBool(false)[pid := true]
}

function {:inline}{:linear "pid"} PidSetCollector (pids:[int]bool) : [int]bool
{
  pids
}
