// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:datatype} Channel; // FIFO channel
function {:constructor} Channel(C: [int]int, head: int, tail: int): Channel;

type ChannelId; // id of a FIFO channel

type {:linear "cid"} {:datatype} ChannelHandle; // permission for sending to or receiving from a channel
function {:constructor} Send(cid: ChannelId): ChannelHandle;
function {:constructor} Receive(cid: ChannelId): ChannelHandle;

function {:inline} Cid(handle: ChannelHandle): ChannelId {
  handle->cid
}

function {:inline} {:linear "cid"} ChannelIdCollector(cid: ChannelId) : [ChannelHandle]bool {
  MapConst(false)[Send(cid) := true][Receive(cid) := true]
}

var {:layer 0,3} channels: [ChannelId]Channel; // pool of FIFO channels

type {:pending_async}{:datatype} PA;
function {:constructor} PRODUCER(x: int, send_handle: ChannelHandle) : PA;
function {:constructor} CONSUMER(x: int, receive_handle: ChannelHandle) : PA;

function {:inline} NoPAs () : [PA]int
{ (lambda pa:PA :: 0) }

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}
{:IS "MAIN'","INV"}{:elim "PRODUCER"}{:elim "CONSUMER","CONSUMER'"}
MAIN ({:linear_in "cid"} cid: ChannelId)
returns ({:pending_async "PRODUCER","CONSUMER"} PAs:[PA]int)
{
  assert channels[cid]->head == channels[cid]->tail;
  PAs := NoPAs()[PRODUCER(1, Send(cid)) := 1][CONSUMER(1, Receive(cid)) := 1];
}

procedure {:atomic}{:layer 3}
MAIN' ({:linear_in "cid"} cid: ChannelId)
modifies channels;
{
  var channel: Channel;

  assert channels[cid]->head == channels[cid]->tail;
  assume channel->head == channel->tail;
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

  assert channels[cid]->head == channels[cid]->tail;

  C := channel->C;
  head := channel->head;
  tail := channel->tail;
  assume {:add_to_pool "INV1", c} 0 < c;
  if (*) {
    assume head == tail;
    PAs := NoPAs()[PRODUCER(c, Send(cid)) := 1][CONSUMER(c, Receive(cid)) := 1];
    choice := PRODUCER(c, Send(cid));
  } else if (*) {
    assume tail == head + 1 && C[head] == 0;
    PAs := NoPAs()[CONSUMER(c, Receive(cid)) := 1];
    choice := CONSUMER(c, Receive(cid));
  } else if (*) {
    assume tail == head + 1 && C[head] == c;
    PAs := NoPAs()[PRODUCER(c+1, Send(cid)) := 1][CONSUMER(c, Receive(cid)) := 1];
    choice := CONSUMER(c, Receive(cid));
  } else {
    assume head == tail;
    PAs := NoPAs();
  }
  channels[cid] := channel;
}

////////////////////////////////////////////////////////////////////////////////

procedure {:left}{:layer 2}
PRODUCER (x: int, {:linear_in "cid"} send_handle: ChannelHandle)
returns ({:pending_async "PRODUCER"} PAs:[PA]int)
modifies channels;
{
  var channel: Channel;
  var C: [int]int;
  var head, tail: int;
  var cid: ChannelId;

  assert send_handle is Send;
  cid := Cid(send_handle);
  channel := channels[cid];
  C := channel->C;
  head := channel->head;
  tail := channel->tail;
  if (*)
  {
    C[tail] := x;
    tail := tail + 1;
    PAs := NoPAs()[PRODUCER(x+1, send_handle) := 1];
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
CONSUMER (x: int, {:linear_in "cid"} receive_handle: ChannelHandle)
returns ({:pending_async "CONSUMER"} PAs:[PA]int)
modifies channels;
{
  var channel: Channel;
  var C: [int]int;
  var head, tail: int;
  var x': int;
  var cid: ChannelId;

  assert receive_handle is Receive;
  cid := Cid(receive_handle);
  channel := channels[cid];
  C := channel->C;
  head := channel->head;
  tail := channel->tail;
  assert head < tail ==> C[head] == x || C[head] == 0;  // assertion to discharge

  assume head < tail;
  x' := C[head];
  head := head + 1;
  if (x' != 0)
  {
    PAs := NoPAs()[CONSUMER(x'+1, receive_handle) := 1];
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
CONSUMER' (x:int, {:linear_in "cid"} receive_handle: ChannelHandle)
returns ({:pending_async "CONSUMER"} PAs:[PA]int)
modifies channels;
{
  var channel: Channel;
  var head, tail: int;
  var cid: ChannelId;

  cid := Cid(receive_handle);
  channel := channels[cid];
  head := channel->head;
  tail := channel->tail;
  assert head < tail;
  call PAs := CONSUMER(x, receive_handle);
}

////////////////////////////////////////////////////////////////////////////////

procedure {:yields}{:layer 1}{:refines "MAIN"}
main ({:linear_in "cid"} cid: ChannelId)
{
  var {:linear "cid"} send_handle, receive_handle: ChannelHandle;

  call send_handle, receive_handle := split(cid);
  async call producer(1, send_handle);
  async call consumer(1, receive_handle);
}

procedure {:yields}{:layer 1}{:refines "PRODUCER"}
producer (x:int, {:linear_in "cid"} send_handle: ChannelHandle)
{
  if (*)
  {
    call send(x, send_handle);
    async call producer(x+1, send_handle);
  }
  else
  {
    call send(0, send_handle);
  }
}

procedure {:yields}{:layer 1}{:refines "CONSUMER"}
consumer (x:int, {:linear_in "cid"} receive_handle: ChannelHandle)
{
  var x': int;

  call x' := receive(receive_handle);
  if (x' != 0)
  {
    assert {:layer 1} x' == x; // low-level assertion to discharge
    async call consumer(x'+1, receive_handle);
  }
}

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 1} SEND (m: int, {:linear "cid"} send_handle: ChannelHandle)
modifies channels;
{
  var channel: Channel;
  var C: [int]int;
  var head, tail: int;
  var cid: ChannelId;

  assert send_handle is Send;
  cid := Cid(send_handle);
  channel := channels[cid];
  C := channel->C;
  head := channel->head;
  tail := channel->tail;
  C[tail] := m;
  tail := tail + 1;
  channels[cid] := Channel(C, head, tail);
}

procedure {:atomic}{:layer 1} RECEIVE ({:linear "cid"} receive_handle: ChannelHandle) returns (m:int)
modifies channels;
{
  var channel: Channel;
  var C: [int]int;
  var head, tail: int;
  var cid: ChannelId;

  assert receive_handle is Receive;
  cid := Cid(receive_handle);
  channel := channels[cid];
  C := channel->C;
  head := channel->head;
  tail := channel->tail;
  assume head < tail;
  m := C[head];
  head := head + 1;
  channels[cid] := Channel(C, head, tail);
}

procedure {:both}{:layer 1} SPLIT({:linear_in "cid"} cid: ChannelId)
  returns ({:linear "cid"} send_handle: ChannelHandle, {:linear "cid"} receive_handle: ChannelHandle)
{
  send_handle := Send(cid);
  receive_handle := Receive(cid);
}

procedure {:yields}{:layer 0}{:refines "SEND"} send (m: int, {:linear "cid"} send_handle: ChannelHandle);
procedure {:yields}{:layer 0}{:refines "RECEIVE"} receive ({:linear "cid"} receive_handle: ChannelHandle) returns (m: int);
procedure {:yields}{:layer 0}{:refines "SPLIT"} split({:linear_in "cid"} cid: ChannelId)
  returns ({:linear "cid"} send_handle: ChannelHandle, {:linear "cid"} receive_handle: ChannelHandle);
