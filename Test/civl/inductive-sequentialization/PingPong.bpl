// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This example shows how to use a bidirectional shared channel to communicate between
// two processes. The modeling of bidirectional channels is generic.
// Its usage is specifically illustrated here on a PingPong example
// containing two processes called Ping and Pong.

// A bidirectional channel is a pair of ordinary channels with two ends---left and right.
// The Ping and Pong processes share a channel pair with Ping holding its left end
// and Pong holding its right end.
datatype ChannelPair { ChannelPair(left: [int]int, right: [int]int) }

// The id type for indexing into the pool of bidirectional channels.
type ChannelId;

// The following global variables models all instances of a bidirectional channel indexed
// the ChannelId type. A single instance of PingPong will only use a single channel id.
var {:layer 0,3} channel: [ChannelId]ChannelPair;

// The id of a bidirectional channel can be split into two permissions---Left and Right.
// Left permission is used to receive from the left channel and send to the right channel.
// Right permission is used to receive from the right channel and send to the left channel.
datatype {:linear "cid"} ChannelHandle { Left(cid: ChannelId), Right(cid: ChannelId) }
function {:inline} ChannelId(p: ChannelHandle) : ChannelId {
  p->cid
}

function {:inline} {:linear "cid"} ChannelIdCollector(cid: ChannelId) : [ChannelHandle]bool {
  MapConst(false)[Left(cid) := true][Right(cid) := true]
}

function {:inline} EmptyChannel () : [int]int
{ (lambda m:int :: 0) }

////////////////////////////////////////////////////////////////////////////////

action {:layer 3}
MAIN' ({:linear_in "cid"} cid: ChannelId)
{
  assert channel[cid] == ChannelPair(EmptyChannel(), EmptyChannel());
}

invariant action {:layer 2}{:elim "PING","PING'"}{:elim "PONG","PONG'"}
INV ({:linear_in "cid"} cid: ChannelId)
creates PING, PONG;
modifies channel;
{
  var {:pool "INV"} c: int;

  assert channel[cid] == ChannelPair(EmptyChannel(), EmptyChannel());

  assume {:add_to_pool "INV", c, c+1} 0 < c;
  if (*) {
    channel[cid] := ChannelPair(EmptyChannel(), EmptyChannel()[c := 1]);
    call create_async(PONG(c, Right(cid)));
    call create_async(PING(c, Left(cid)));
    call set_choice(PONG(c, Right(cid)));
  } else if (*) {
    channel[cid] := ChannelPair(EmptyChannel(), EmptyChannel()[0 := 1]);
    call create_async(PONG(c, Right(cid)));
    call set_choice(PONG(c, Right(cid)));
  } else if (*) {
    channel[cid] := ChannelPair(EmptyChannel()[c := 1], EmptyChannel());
    call create_async(PONG(c+1, Right(cid)));
    call create_async(PING(c, Left(cid)));
    call set_choice(PING(c, Left(cid)));
  } else {
    channel[cid] := ChannelPair(EmptyChannel(), EmptyChannel());
  }
}

////////////////////////////////////////////////////////////////////////////////

abstract action {:layer 2} PING' (x: int, {:linear_in "cid"} left: ChannelHandle)
creates PING;
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
  call PING(x, left);

}

abstract action {:layer 2} PONG' (y: int, {:linear_in "cid"} right: ChannelHandle)
creates PONG;
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
  call PONG(y, right);
}

////////////////////////////////////////////////////////////////////////////////

action {:layer 2} MAIN ({:linear_in "cid"} cid: ChannelId) refines MAIN' using INV
creates PING, PONG;
modifies channel;
{
  assert channel[cid] == ChannelPair(EmptyChannel(), EmptyChannel());
  channel[cid] := ChannelPair(EmptyChannel(), EmptyChannel()[1 := 1]);
  call create_async(PING(1, Left(cid)));
  call create_async(PONG(1, Right(cid)));
}

async action {:layer 2} PING (x: int, {:linear_in "cid"} left: ChannelHandle)
creates PING;
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
    call create_async(PING(x+1, left));
  }
  else
  {
    right_channel[0] := right_channel[0] + 1;
  }
  channel[cid] := ChannelPair(left_channel, right_channel);
}

async action {:layer 2} PONG (y: int, {:linear_in "cid"} right: ChannelHandle)
creates PONG;
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
    call create_async(PONG(y+1, right));
  }
  else
  {
    assume right_channel[0] > 0;
    right_channel[0] := right_channel[0] - 1;
  }
  channel[cid] := ChannelPair(left_channel, right_channel);
}

////////////////////////////////////////////////////////////////////////////////

yield procedure {:layer 1}
main ({:linear_in "cid"} cid: ChannelId) refines MAIN
{
  var {:linear "cid"} left: ChannelHandle;
  var {:linear "cid"} right: ChannelHandle;

  call left, right := split(cid);
  call send(left, 1);
  async call ping(1, left);
  async call pong(1, right);
}

yield procedure {:layer 1}
ping (x: int, {:linear_in "cid"} left: ChannelHandle) refines PING
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

yield procedure {:layer 1}
pong (y: int, {:linear_in "cid"} right: ChannelHandle) refines PONG
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

-> action {:layer 1} RECEIVE (permission: ChannelHandle) returns (m: int)
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

<- action {:layer 1} SEND (permission: ChannelHandle, m: int)
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

<-> action {:layer 1} SPLIT({:linear_in "cid"} cid: ChannelId)
  returns ({:linear "cid"} left: ChannelHandle, {:linear "cid"} right: ChannelHandle)
{
  left := Left(cid);
  right := Right(cid);
}

yield procedure {:layer 0} receive (permission: ChannelHandle) returns (m: int) refines RECEIVE;
yield procedure {:layer 0} send (permission: ChannelHandle, m: int) refines SEND;
yield procedure {:layer 0} split({:linear_in "cid"} cid: ChannelId)
  returns ({:linear "cid"} left: ChannelHandle, {:linear "cid"} right: ChannelHandle) refines SPLIT;
