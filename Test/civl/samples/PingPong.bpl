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
var {:layer 0,1} channels: [ChannelId]ChannelPair;

// The id of a bidirectional channel can be split into two permissions---Left and Right.
// Left permission is used to receive from the left channel and send to the right channel.
// Right permission is used to receive from the right channel and send to the left channel.
datatype ChannelHandle { Left(cid: ChannelId), Right(cid: ChannelId) }

function {:inline} BothHandles(cid: ChannelId): Set ChannelHandle
{ Set_Add(Set_Singleton(Left(cid)), Right(cid)) }

function {:inline} Empty() : [int]int { MapConst(0) }

function {:inline} Singleton(x: int): [int]int { Empty()[x := 1] }

////////////////////////////////////////////////////////////////////////////////

yield invariant {:layer 1} YieldMain(cid: ChannelId, {:linear} handles: Set ChannelHandle);
preserves handles == BothHandles(cid);
preserves channels[cid] == ChannelPair(Empty(), Empty());

yield invariant {:layer 1} YieldPing(x: int, {:linear} p: One ChannelHandle);
preserves p->val is Left;
preserves x > 0;
preserves (var left_channel, right_channel := channels[p->val->cid]->left, channels[p->val->cid]->right;
            (left_channel == Empty() && right_channel == Singleton(x) && x > 0) ||
            (left_channel == Singleton(x) && right_channel == Empty()));

yield invariant {:layer 1} YieldPong(y: int, {:linear} p: One ChannelHandle);
preserves p->val is Right;
preserves y > 0;
preserves (var left_channel, right_channel := channels[p->val->cid]->left, channels[p->val->cid]->right;
            (left_channel == Empty() && (right_channel == Singleton(y) || right_channel == Singleton(0))) ||
            (left_channel == Singleton(y-1) && right_channel == Empty()));

////////////////////////////////////////////////////////////////////////////////

yield procedure {:layer 1}
main (cid: ChannelId, {:linear_in} handles: Set ChannelHandle)
requires call YieldMain(cid, handles);
{
  var {:linear} handles': Set ChannelHandle;
  var {:linear} left: One ChannelHandle;
  var {:linear} right: One ChannelHandle;

  handles' := handles;
  left := One(Left(cid));
  call One_Split(handles', left);
  right := One(Right(cid));
  call One_Split(handles', right);
  call send(left->val, 1);
  async call ping(1, left);
  async call pong(1, right);
}

yield procedure {:layer 1}
ping (x: int, {:linear_in} p: One ChannelHandle)
requires call YieldPing(x, p);
{
  var x': int;

  call x' := receive(p->val);
  assert {:layer 1} x' == x; // low-level assertion to discharge
  if (*)
  {
    call send(p->val, x'+1);
    async call ping(x'+1, p);
  }
  else
  {
    call send(p->val, 0);
  }
}

yield procedure {:layer 1}
pong (y: int, {:linear_in} p: One ChannelHandle)
requires call YieldPong(y, p);
{
  var y': int;

  call y' := receive(p->val);
  if (y' != 0)
  {
    assert {:layer 1} y' == y; // low-level assertion to discharge
    call send(p->val, y');
    async call pong(y'+1, p);
  }
}

////////////////////////////////////////////////////////////////////////////////
// Bidirectional channels

yield procedure {:layer 0} receive (p: ChannelHandle) returns (m: int);
refines right action {:layer 1} _ {
  var left_channel: [int]int;
  var right_channel: [int]int;

  left_channel := channels[p->cid]->left;
  right_channel := channels[p->cid]->right;
  if (p is Left) {
    assume left_channel[m] > 0;
    left_channel[m] := left_channel[m] - 1;
  } else {
    assume right_channel[m] > 0;
    right_channel[m] := right_channel[m] - 1;
  }
  channels[p->cid] := ChannelPair(left_channel, right_channel);
}

yield procedure {:layer 0} send (p: ChannelHandle, m: int);
refines left action {:layer 1} _ {
  var left_channel: [int]int;
  var right_channel: [int]int;

  left_channel := channels[p->cid]->left;
  right_channel := channels[p->cid]->right;
  if (p is Left) {
    right_channel[m] := right_channel[m] + 1;
  } else {
    left_channel[m] := left_channel[m] + 1;
  }
  channels[p->cid] := ChannelPair(left_channel, right_channel);
}
