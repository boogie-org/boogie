// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "pid"} Pid = int;
var {:layer 0,3} ping_channel:[int]int; // Incoming channel of Ping
var {:layer 0,3} pong_channel:[int]int; // Incoming channel of Pong

const unique ping_id:int;
const unique pong_id:int;

type {:pending_async}{:datatype} PA;
function {:pending_async "PING"}{:constructor} PING_PA(x:int, pid:int) : PA;
function {:pending_async "PONG"}{:constructor} PONG_PA(x:int, pid:int) : PA;

function trigger(x:int) : bool { true }

function {:inline} NoPAs () : [PA]int
{ (lambda pa:PA :: 0) }

function {:inline} EmptyChannel () : [int]int
{ (lambda m:int :: 0) }

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 3}
MAIN' ({:linear_in "pid"} ping_pid:int, {:linear_in "pid"} pong_pid:int)
{
  assert ping_pid == ping_id;
  assert pong_pid == pong_id;
  assert ping_channel == EmptyChannel();
  assert pong_channel == EmptyChannel();
}

procedure {:IS_invariant}{:layer 2}
INV ({:linear_in "pid"} ping_pid:int, {:linear_in "pid"} pong_pid:int)
returns ({:pending_async "PING","PONG"} PAs:[PA]int, {:choice} choice:PA)
modifies ping_channel, pong_channel;
{
  assert ping_pid == ping_id;
  assert pong_pid == pong_id;
  assert ping_channel == EmptyChannel();
  assert pong_channel == EmptyChannel();

  havoc ping_channel, pong_channel;

  assume
  (exists c:int :: {trigger(c)} c > 0 && trigger(c) && trigger(c+1) &&
    (
      (pong_channel == EmptyChannel()[c := 1] && ping_channel == EmptyChannel() &&
       PAs == NoPAs()[PONG_PA(c, pong_pid) := 1][PING_PA(c, ping_pid) := 1] &&
       choice == PONG_PA(c, pong_pid))
      ||
      (pong_channel == EmptyChannel()[0 := 1] && ping_channel == EmptyChannel() &&
       PAs == NoPAs()[PONG_PA(c, pong_pid) := 1] &&
       choice == PONG_PA(c, pong_pid))
      ||
      (ping_channel == EmptyChannel()[c := 1] && pong_channel == EmptyChannel() &&
       PAs == NoPAs()[PONG_PA(c+1, pong_pid) := 1][PING_PA(c, ping_pid) := 1] &&
       choice == PING_PA(c, ping_pid))
      ||
      (ping_channel == EmptyChannel() && pong_channel == EmptyChannel() &&
       PAs == NoPAs())
    )
  );
}

////////////////////////////////////////////////////////////////////////////////

procedure {:IS_abstraction}{:layer 2}
PING' (x:int, {:linear_in "pid"} pid:int)
returns ({:pending_async "PING"} PAs:[PA]int)
modifies ping_channel, pong_channel;
{
  assert x > 0;
  assert pid == ping_id;
  assert (forall m:int :: ping_channel[m] > 0 ==> m == x);
  assert (exists m:int :: ping_channel[m] > 0) && (forall m:int :: pong_channel[m] == 0);

  assume ping_channel[x] > 0;
  ping_channel[x] := ping_channel[x] - 1;

  if (*)
  {
    pong_channel[x+1] := pong_channel[x+1] + 1;
    PAs := NoPAs()[PING_PA(x+1, pid) := 1];
  }
  else
  {
    pong_channel[0] := pong_channel[0] + 1;
    PAs := NoPAs();
  }
}

procedure {:IS_abstraction}{:layer 2}
PONG' (y:int, {:linear_in "pid"} pid:int)
returns ({:pending_async "PONG"} PAs:[PA]int)
modifies ping_channel, pong_channel;
{
  assert y > 0;
  assert pid == pong_id;
  assert (forall m:int :: pong_channel[m] > 0 ==> m == y || m == 0);
  assert (exists m:int :: pong_channel[m] > 0) && (forall m:int :: ping_channel[m] == 0);

  if (*)
  {
    assume pong_channel[y] > 0;
    pong_channel[y] := pong_channel[y] - 1;
    ping_channel[y] := ping_channel[y] + 1;
    PAs := NoPAs()[PONG_PA(y+1, pid) := 1];
  }
  else
  {
    assume pong_channel[0] > 0;
    pong_channel[0] := pong_channel[0] - 1;
    PAs := NoPAs();
  }
}

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}
{:IS "MAIN'","INV"}{:elim "PING","PING'"}{:elim "PONG","PONG'"}
MAIN ({:linear_in "pid"} ping_pid:int, {:linear_in "pid"} pong_pid:int)
returns ({:pending_async "PING","PONG"} PAs:[PA]int)
modifies pong_channel;
{
  assert ping_pid == ping_id;
  assert pong_pid == pong_id;
  assert ping_channel == EmptyChannel();
  assert pong_channel == EmptyChannel();
  assert trigger(1);
  pong_channel[1] := pong_channel[1] + 1;
  PAs := NoPAs()[PING_PA(1, ping_pid) := 1][PONG_PA(1, pong_pid) := 1];
}

procedure {:atomic}{:layer 2}
PING (x:int, {:linear_in "pid"} pid:int)
returns ({:pending_async "PING"} PAs:[PA]int)
modifies ping_channel, pong_channel;
{
  assert x > 0;
  assert pid == ping_id;
  assert (forall m:int :: ping_channel[m] > 0 ==> m == x); // assertion to discharge

  assume ping_channel[x] > 0;
  ping_channel[x] := ping_channel[x] - 1;

  if (*)
  {
    pong_channel[x+1] := pong_channel[x+1] + 1;
    PAs := NoPAs()[PING_PA(x+1, pid) := 1];
  }
  else
  {
    pong_channel[0] := pong_channel[0] + 1;
    PAs := NoPAs();
  }
}

procedure {:atomic}{:layer 2}
PONG (y:int, {:linear_in "pid"} pid:int)
returns ({:pending_async "PONG"} PAs:[PA]int)
modifies ping_channel, pong_channel;
{
  assert y > 0;
  assert pid == pong_id;
  assert (forall m:int :: pong_channel[m] > 0 ==> m == y || m == 0); // assertion to discharge

  if (*)
  {
    assume pong_channel[y] > 0;
    pong_channel[y] := pong_channel[y] - 1;
    ping_channel[y] := ping_channel[y] + 1;
    PAs := NoPAs()[PONG_PA(y+1, pid) := 1];
  }
  else
  {
    assume pong_channel[0] > 0;
    pong_channel[0] := pong_channel[0] - 1;
    PAs := NoPAs();
  }
}

////////////////////////////////////////////////////////////////////////////////

procedure {:yields}{:layer 1}{:refines "MAIN"}
main ({:linear_in "pid"} ping_pid:int, {:linear_in "pid"} pong_pid:int)
{
  call send_pong_channel(1);
  async call ping(1, ping_pid);
  async call pong(1, pong_pid);
}

procedure {:yields}{:layer 1}{:refines "PING"}
ping (x:int, {:linear_in "pid"} pid:int)
{
  var x':int;

  call x' := receive_ping_channel();
  call assert_eq(x', x); // low-level assertion to discharge
  if (*)
  {
    call send_pong_channel(x'+1);
    async call ping(x'+1, pid);
  }
  else
  {
    call send_pong_channel(0);
  }
}

procedure {:yields}{:layer 1}{:refines "PONG"}
pong (y:int, {:linear_in "pid"} pid:int)
{
  var y':int;

  call y' := receive_pong_channel();
  if (y' != 0)
  {
    call assert_eq(y', y); // low-level assertion to discharge
    call send_ping_channel(y');
    async call pong(y'+1, pid);
  }
}

////////////////////////////////////////////////////////////////////////////////

procedure {:left}{:layer 1} SEND_PING_CHANNEL (m:int)
modifies ping_channel;
{
  ping_channel[m] := ping_channel[m] + 1;
}

procedure {:left}{:layer 1} SEND_PONG_CHANNEL (m:int)
modifies pong_channel;
{
  pong_channel[m] := pong_channel[m] + 1;
}

procedure {:right}{:layer 1} RECEIVE_PING_CHANNEL () returns (m:int)
modifies ping_channel;
{
  assume ping_channel[m] > 0;
  ping_channel[m] := ping_channel[m] - 1;
}

procedure {:right}{:layer 1} RECEIVE_PONG_CHANNEL () returns (m:int)
modifies pong_channel;
{
  assume pong_channel[m] > 0;
  pong_channel[m] := pong_channel[m] - 1;
}

procedure {:both}{:layer 1} ASSERT_EQ (a:int, b:int)
{
  assert a == b;
}

procedure {:yields}{:layer 0}{:refines "SEND_PING_CHANNEL"} send_ping_channel (m:int);
procedure {:yields}{:layer 0}{:refines "SEND_PONG_CHANNEL"} send_pong_channel (m:int);
procedure {:yields}{:layer 0}{:refines "RECEIVE_PING_CHANNEL"} receive_ping_channel () returns (m:int);
procedure {:yields}{:layer 0}{:refines "RECEIVE_PONG_CHANNEL"} receive_pong_channel () returns (m:int);
procedure {:yields}{:layer 0}{:refines "ASSERT_EQ"} assert_eq (a:int, b:int);
