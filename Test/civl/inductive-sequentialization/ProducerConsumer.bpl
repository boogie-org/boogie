// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:datatype} Channel; // FIFO channel
function {:constructor} Channel(C: [int]int, head: int, tail: int): Channel;

type ChannelId; // id of a FIFO channel

type {:linear "cid"} {:datatype} ChannelHandle; // permission for sending to or receiving from a channel
function {:constructor} Send(cid: ChannelId): ChannelHandle;
function {:constructor} Receive(cid: ChannelId): ChannelHandle;
function {:inline} {:linear "cid"} ChannelIdCollector(cid: ChannelId) : [ChannelHandle]bool {
  MapConst(false)[Send(cid) := true][Receive(cid) := true]
}

var {:layer 0,3} channels: [ChannelId]Channel; // pool of FIFO channels

type {:pending_async}{:datatype} PA;
function {:constructor} PRODUCER(x: int, cid: ChannelId, send: ChannelHandle) : PA;
function {:constructor} CONSUMER(x: int, cid: ChannelId, receive: ChannelHandle) : PA;

function {:inline} NoPAs () : [PA]int
{ (lambda pa:PA :: 0) }

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}
{:IS "MAIN'","INV"}{:elim "PRODUCER"}{:elim "CONSUMER","CONSUMER'"}
MAIN ({:linear_in "cid"} cid: ChannelId)
returns ({:pending_async "PRODUCER","CONSUMER"} PAs:[PA]int)
{
  assert head#Channel(channels[cid]) == tail#Channel(channels[cid]);
  PAs := NoPAs()[PRODUCER(1, cid, Send(cid)) := 1][CONSUMER(1, cid, Receive(cid)) := 1];
}

procedure {:atomic}{:layer 3}
MAIN' ({:linear_in "cid"} cid: ChannelId)
modifies channels;
{
  var channel: Channel;

  assert head#Channel(channels[cid]) == tail#Channel(channels[cid]);
  channels[cid] := channel;
}

procedure {:IS_invariant}{:layer 2}
INV ({:linear_in "cid"} cid: ChannelId)
returns ({:pending_async "PRODUCER","CONSUMER"} PAs:[PA]int, {:choice} choice:PA)
modifies channels;
{
  var {:pool "INV1"} c: int;
  var {:pool "INV2"} channel: Channel;
  var C: [int]int;
  var head, tail: int;

  assert head#Channel(channels[cid]) == tail#Channel(channels[cid]);
  channels[cid] := channel;
  C := C#Channel(channel);
  head := head#Channel(channel);
  tail := tail#Channel(channel);

  assume {:add_to_pool "INV1", c} 0 < c;
  if (*) {
    assume head == tail;
    PAs := NoPAs()[PRODUCER(c, cid, Send(cid)) := 1][CONSUMER(c, cid, Receive(cid)) := 1];
    choice := PRODUCER(c, cid, Send(cid));
  } else if (*) {
    assume tail == head + 1 && C[head] == 0;
    PAs := NoPAs()[CONSUMER(c, cid, Receive(cid)) := 1];
    choice := CONSUMER(c, cid, Receive(cid));
  } else if (*) {
    assume tail == head + 1 && C[head] == c;
    PAs := NoPAs()[PRODUCER(c+1, cid, Send(cid)) := 1][CONSUMER(c, cid, Receive(cid)) := 1];
    choice := CONSUMER(c, cid, Receive(cid));
  } else {
    assume head == tail;
    PAs := NoPAs();
  }
}

////////////////////////////////////////////////////////////////////////////////

procedure {:left}{:layer 2}
PRODUCER (x: int, cid: ChannelId, {:linear_in "cid"} send: ChannelHandle)
returns ({:pending_async "PRODUCER"} PAs:[PA]int)
modifies channels;
{
  var channel: Channel;
  var C: [int]int;
  var head, tail: int;

  assert send == Send(cid);
  channel := channels[cid];
  C := C#Channel(channel);
  head := head#Channel(channel);
  tail := tail#Channel(channel);
  if (*)
  {
    C[tail] := x;
    tail := tail + 1;
    PAs := NoPAs()[PRODUCER(x+1, cid, send) := 1];
  }
  else
  {
    C[tail] := 0;
    tail := tail + 1;
    PAs := NoPAs();
  }
  channels[cid] := Channel(C, head, tail);
  assume {:add_to_pool "INV2", channels[cid]} true;
}

procedure {:atomic}{:layer 2}
CONSUMER (x: int, cid: ChannelId, {:linear_in "cid"} receive: ChannelHandle)
returns ({:pending_async "CONSUMER"} PAs:[PA]int)
modifies channels;
{
  var channel: Channel;
  var C: [int]int;
  var head, tail: int;
  var x': int;

  assert receive == Receive(cid);
  channel := channels[cid];
  C := C#Channel(channel);
  head := head#Channel(channel);
  tail := tail#Channel(channel);
  assert head < tail ==> C[head] == x || C[head] == 0;  // assertion to discharge

  assume head < tail;
  x' := C[head];
  head := head + 1;
  if (x' != 0)
  {
    PAs := NoPAs()[CONSUMER(x'+1, cid, receive) := 1];
  }
  else
  {
    PAs := NoPAs();
  }
  channels[cid] := Channel(C, head, tail);
  assume {:add_to_pool "INV2", channels[cid]} true;
}

////////////////////////////////////////////////////////////////////////////////

procedure {:IS_abstraction}{:layer 2}
CONSUMER' (x:int, cid: ChannelId, {:linear_in "cid"} receive: ChannelHandle)
returns ({:pending_async "CONSUMER"} PAs:[PA]int)
modifies channels;
{
  var channel: Channel;
  var head, tail: int;

  channel := channels[cid];
  head := head#Channel(channel);
  tail := tail#Channel(channel);
  assert head < tail;
  call PAs := CONSUMER(x, cid, receive);
}

////////////////////////////////////////////////////////////////////////////////

procedure {:yields}{:layer 1}{:refines "MAIN"}
main ({:linear_in "cid"} cid: ChannelId)
{
  var {:linear "cid"} send, receive: ChannelHandle;

  call send, receive := split(cid);
  async call producer(1, cid, send);
  async call consumer(1, cid, receive);
}

procedure {:yields}{:layer 1}{:refines "PRODUCER"}
producer (x:int, cid: ChannelId, {:linear_in "cid"} send: ChannelHandle)
{
  if (*)
  {
    call send(x, cid, send);
    async call producer(x+1, cid, send);
  }
  else
  {
    call send(0, cid, send);
  }
}

procedure {:yields}{:layer 1}{:refines "CONSUMER"}
consumer (y:int, cid: ChannelId, {:linear_in "cid"} receive: ChannelHandle)
{
  var y': int;

  call y' := receive(cid, receive);
  if (y' != 0)
  {
    assert {:layer 1} y' == y; // low-level assertion to discharge
    async call consumer(y'+1, cid, receive);
  }
}

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 1} SEND (m: int, cid: ChannelId, {:linear "cid"} send: ChannelHandle)
modifies channels;
{
  var channel: Channel;
  var C: [int]int;
  var head, tail: int;

  assert send == Send(cid);
  channel := channels[cid];
  C := C#Channel(channel);
  head := head#Channel(channel);
  tail := tail#Channel(channel);
  C[tail] := m;
  tail := tail + 1;
  channels[cid] := Channel(C, head, tail);
}

procedure {:atomic}{:layer 1} RECEIVE (cid: ChannelId, {:linear "cid"} receive: ChannelHandle) returns (m:int)
modifies channels;
{
  var channel: Channel;
  var C: [int]int;
  var head, tail: int;

  assert receive == Receive(cid);
  channel := channels[cid];
  C := C#Channel(channel);
  head := head#Channel(channel);
  tail := tail#Channel(channel);
  assume head < tail;
  m := C[head];
  head := head + 1;
  channels[cid] := Channel(C, head, tail);
}

procedure {:both}{:layer 1} SPLIT({:linear_in "cid"} cid: ChannelId)
  returns ({:linear "cid"} send: ChannelHandle, {:linear "cid"} receive: ChannelHandle)
{
  send := Send(cid);
  receive := Receive(cid);
}

procedure {:yields}{:layer 0}{:refines "SEND"} send (m: int, cid: ChannelId, {:linear "cid"} send: ChannelHandle);
procedure {:yields}{:layer 0}{:refines "RECEIVE"} receive (cid: ChannelId, {:linear "cid"} receive: ChannelHandle) returns (m: int);
procedure {:yields}{:layer 0}{:refines "SPLIT"} split({:linear_in "cid"} cid: ChannelId)
  returns ({:linear "cid"} send: ChannelHandle, {:linear "cid"} receive: ChannelHandle);
