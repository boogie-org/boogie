// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This example shows how to use a bidirectional shared channel to communicate between
// two processes. The modeling of bidirectional channels is generic.
// Its usage is specifically illustrated here on a PingPong example.

// A bidirectional channel is a pair of ordinary channels with two ends---left and right.
type {:datatype} ChannelPair;
function {:constructor} ChannelPair(left: [int]int, right: [int]int): ChannelPair;

// The id type for indexing into the pool of bidirectional channels.
type ChannelId;

// The following global variables models al instances of a bidirectional channel indexed
// the ChannelId type. A single instance of PingPong will only use a single channel id.
var {:layer 0,3} channel: [ChannelId]ChannelPair;

// The id of a bidirectional channel can be split into two permissions---Left and Right.
// Left permission is used to receive from the left channel and send to the right channel.
// Right permission is used to receive from the right channel and send to the left channel.
type {:linear "cid"} {:datatype} ChannelHandle;
function {:constructor} Left(cid: ChannelId): ChannelHandle;
function {:constructor} Right(cid: ChannelId): ChannelHandle;
function {:inline} ChannelId(p: ChannelHandle) : ChannelId {
  p->cid
}

function {:inline} {:linear "cid"} ChannelIdCollector(cid: ChannelId) : [ChannelHandle]bool {
  MapConst(false)[Left(cid) := true][Right(cid) := true]
}

// This datatype declares the pending asyncs for Ping and Pong processes.
// These two processes share a channel pair with Ping holding its left channel handle
// and Pong holding its right channel handle.
type {:pending_async}{:datatype} PA;
function {:constructor} PING(x: int, left: ChannelHandle): PA;
function {:constructor} PONG(y: int, right: ChannelHandle): PA;

function {:inline} NoPAs () : [PA]int
{ (lambda pa:PA :: 0) }

function {:inline} EmptyChannel () : [int]int
{ (lambda m:int :: 0) }

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 3}
MAIN' ({:linear_in "cid"} cid: ChannelId)
{
  assert channel[cid] == ChannelPair(EmptyChannel(), EmptyChannel());
}

procedure {:IS_invariant}{:layer 2}
INV ({:linear_in "cid"} cid: ChannelId)
returns ({:pending_async "PING","PONG"} PAs: [PA]int, {:choice} choice: PA)
modifies channel;
{
  var {:pool "INV"} c: int;

  assert channel[cid] == ChannelPair(EmptyChannel(), EmptyChannel());

  assume
    {:add_to_pool "INV", c, c+1}
    0 < c;
  if (*) {
    channel[cid] := ChannelPair(EmptyChannel(), EmptyChannel()[c := 1]);
    PAs := NoPAs()[PONG(c, Right(cid)) := 1][PING(c, Left(cid)) := 1];
    choice := PONG(c, Right(cid));
  } else if (*) {
    channel[cid] := ChannelPair(EmptyChannel(), EmptyChannel()[0 := 1]);
    PAs := NoPAs()[PONG(c, Right(cid)) := 1];
    choice := PONG(c, Right(cid));
  } else if (*) {
    channel[cid] := ChannelPair(EmptyChannel()[c := 1], EmptyChannel());
    PAs := NoPAs()[PONG(c+1, Right(cid)) := 1][PING(c, Left(cid)) := 1];
    choice := PING(c, Left(cid));
  } else {
    channel[cid] := ChannelPair(EmptyChannel(), EmptyChannel());
    PAs := NoPAs();
  }
}

////////////////////////////////////////////////////////////////////////////////

procedure {:IS_abstraction}{:layer 2}
PING' (x: int, {:linear_in "cid"} left: ChannelHandle)
returns ({:pending_async "PING"} PAs: [PA]int)
modifies channel;
{
  var cid: ChannelId;
  var left_channel: [int]int;
  var right_channel: [int]int;

  cid := ChannelId(left);
  left_channel := channel[cid]->left;
  right_channel := channel[cid]->right;

  assert (exists {:pool "INV"} m:int :: left_channel[m] > 0);
  assert (forall m:int :: right_channel[m] == 0);
  call PAs := PING(x, left);

}

procedure {:IS_abstraction}{:layer 2}
PONG' (y: int, {:linear_in "cid"} right: ChannelHandle)
returns ({:pending_async "PONG"} PAs: [PA]int)
modifies channel;
{
  var cid: ChannelId;
  var left_channel: [int]int;
  var right_channel: [int]int;

  cid := ChannelId(right);
  left_channel := channel[cid]->left;
  right_channel := channel[cid]->right;

  assert (exists {:pool "INV"} m:int :: right_channel[m] > 0);
  assert (forall m:int :: left_channel[m] == 0);
  call PAs := PONG(y, right);
}

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}
{:IS "MAIN'","INV"}{:elim "PING","PING'"}{:elim "PONG","PONG'"}
MAIN ({:linear_in "cid"} cid: ChannelId)
returns ({:pending_async "PING","PONG"} PAs: [PA]int)
modifies channel;
{
  assert channel[cid] == ChannelPair(EmptyChannel(), EmptyChannel());
  channel[cid] := ChannelPair(EmptyChannel(), EmptyChannel()[1 := 1]);
  PAs := NoPAs()[PING(1, Left(cid)) := 1][PONG(1, Right(cid)) := 1];
}

procedure {:atomic}{:layer 2}
PING (x: int, {:linear_in "cid"} left: ChannelHandle)
returns ({:pending_async "PING"} PAs: [PA]int)
modifies channel;
{
  var cid: ChannelId;
  var left_channel: [int]int;
  var right_channel: [int]int;

  cid := ChannelId(left);
  left_channel := channel[cid]->left;
  right_channel := channel[cid]->right;

  assert x > 0;
  assert left is Left;
  assert (forall m:int :: left_channel[m] > 0 ==> m == x); // assertion to discharge

  assume left_channel[x] > 0;
  left_channel[x] := left_channel[x] - 1;

  if (*)
  {
    right_channel[x+1] := right_channel[x+1] + 1;
    PAs := NoPAs()[PING(x+1, left) := 1];
  }
  else
  {
    right_channel[0] := right_channel[0] + 1;
    PAs := NoPAs();
  }
  channel[cid] := ChannelPair(left_channel, right_channel);
}

procedure {:atomic}{:layer 2}
PONG (y: int, {:linear_in "cid"} right: ChannelHandle)
returns ({:pending_async "PONG"} PAs: [PA]int)
modifies channel;
{
  var cid: ChannelId;
  var left_channel: [int]int;
  var right_channel: [int]int;

  cid := ChannelId(right);
  left_channel := channel[cid]->left;
  right_channel := channel[cid]->right;

  assert y > 0;
  assert right is Right;
  assert (forall m:int :: right_channel[m] > 0 ==> m == y || m == 0); // assertion to discharge

  if (*)
  {
    assume right_channel[y] > 0;
    right_channel[y] := right_channel[y] - 1;
    left_channel[y] := left_channel[y] + 1;
    PAs := NoPAs()[PONG(y+1, right) := 1];
  }
  else
  {
    assume right_channel[0] > 0;
    right_channel[0] := right_channel[0] - 1;
    PAs := NoPAs();
  }
  channel[cid] := ChannelPair(left_channel, right_channel);
}

////////////////////////////////////////////////////////////////////////////////

procedure {:yields}{:layer 1}{:refines "MAIN"}
main ({:linear_in "cid"} cid: ChannelId)
{
  var {:linear "cid"} left: ChannelHandle;
  var {:linear "cid"} right: ChannelHandle;

  call left, right := split(cid);
  call send(left, 1);
  async call ping(1, left);
  async call pong(1, right);
}

procedure {:yields}{:layer 1}{:refines "PING"}
ping (x: int, {:linear_in "cid"} left: ChannelHandle)
{
  var x': int;

  call x' := receive(left);
  assert {:layer 1} x' == x; // low-level assertion to discharge
  if (*)
  {
    call send(left, x'+1);
    async call ping(x'+1, left);
  }
  else
  {
    call send(left, 0);
  }
}

procedure {:yields}{:layer 1}{:refines "PONG"}
pong (y: int, {:linear_in "cid"} right: ChannelHandle)
{
  var y': int;

  call y' := receive(right);
  if (y' != 0)
  {
    assert {:layer 1} y' == y; // low-level assertion to discharge
    call send(right, y');
    async call pong(y'+1, right);
  }
}

////////////////////////////////////////////////////////////////////////////////
// Bidirectional channels

procedure {:right}{:layer 1} RECEIVE (permission: ChannelHandle) returns (m: int)
modifies channel;
{
  var cid: ChannelId;
  var left_channel: [int]int;
  var right_channel: [int]int;

  cid := ChannelId(permission);
  left_channel := channel[cid]->left;
  right_channel := channel[cid]->right;
  if (permission is Left) {
    assume left_channel[m] > 0;
    left_channel[m] := left_channel[m] - 1;
  } else {
    assume right_channel[m] > 0;
    right_channel[m] := right_channel[m] - 1;
  }
  channel[cid] := ChannelPair(left_channel, right_channel);
}

procedure {:left}{:layer 1} SEND (permission: ChannelHandle, m: int)
modifies channel;
{
  var cid: ChannelId;
  var left_channel: [int]int;
  var right_channel: [int]int;

  cid := ChannelId(permission);
  left_channel := channel[cid]->left;
  right_channel := channel[cid]->right;
  if (permission is Left) {
    right_channel[m] := right_channel[m] + 1;
  } else {
    left_channel[m] := left_channel[m] + 1;
  }
  channel[cid] := ChannelPair(left_channel, right_channel);
}

procedure {:both}{:layer 1} SPLIT({:linear_in "cid"} cid: ChannelId)
  returns ({:linear "cid"} left: ChannelHandle, {:linear "cid"} right: ChannelHandle)
{
  left := Left(cid);
  right := Right(cid);
}

procedure {:yields}{:layer 0}{:refines "RECEIVE"} receive (permission: ChannelHandle) returns (m: int);
procedure {:yields}{:layer 0}{:refines "SEND"} send (permission: ChannelHandle, m: int);
procedure {:yields}{:layer 0}{:refines "SPLIT"} split({:linear_in "cid"} cid: ChannelId)
  returns ({:linear "cid"} left: ChannelHandle, {:linear "cid"} right: ChannelHandle);
