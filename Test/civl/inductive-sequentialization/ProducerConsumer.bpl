// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// FIFO channel
datatype Channel { Channel(C: [int]int, head: int, tail: int) }

// id of a FIFO channel
type ChannelId;

// permission for sending to or receiving from a channel
datatype {:linear "cid"} ChannelHandle { Send(cid: ChannelId), Receive(cid: ChannelId) }

function {:inline} Cid(handle: ChannelHandle): ChannelId {
  handle->cid
}

function {:inline} {:linear "cid"} ChannelIdCollector(cid: ChannelId) : [ChannelHandle]bool {
  MapConst(false)[Send(cid) := true][Receive(cid) := true]
}

// pool of FIFO channels
var {:layer 0,3} channels: [ChannelId]Channel;

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}
{:creates "PRODUCER","CONSUMER"}
{:IS "MAIN'","INV"}
MAIN ({:linear_in "cid"} cid: ChannelId)
{
  assert channels[cid]->head == channels[cid]->tail;
  call create_async(PRODUCER(1, Send(cid)));
  call create_async(CONSUMER(1, Receive(cid)));
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

procedure {:layer 2}
{:creates "PRODUCER","CONSUMER"}
{:IS_invariant}{:elim "PRODUCER"}{:elim "CONSUMER","CONSUMER'"}
INV ({:linear_in "cid"} cid: ChannelId)
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
    call create_async(PRODUCER(c, Send(cid)));
    call create_async(CONSUMER(c, Receive(cid)));
    call set_choice(PRODUCER(c, Send(cid)));
  } else if (*) {
    assume tail == head + 1 && C[head] == 0;
    call create_async(CONSUMER(c, Receive(cid)));
    call set_choice(CONSUMER(c, Receive(cid)));
  } else if (*) {
    assume tail == head + 1 && C[head] == c;
    call create_async(PRODUCER(c+1, Send(cid)));
    call create_async(CONSUMER(c, Receive(cid)));
    call set_choice(CONSUMER(c, Receive(cid)));
  } else {
    assume head == tail;
  }
  channels[cid] := channel;
}

////////////////////////////////////////////////////////////////////////////////

procedure {:left}{:layer 2}
{:pending_async}
{:creates "PRODUCER"}
PRODUCER (x: int, {:linear_in "cid"} send_handle: ChannelHandle)
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
    call create_async(PRODUCER(x+1, send_handle));
  }
  else
  {
    C[tail] := 0;
    tail := tail + 1;
  }
  channels[cid] := Channel(C, head, tail);
  assume {:add_to_pool "INV2", channels[cid]} true;
}

procedure {:atomic}{:layer 2}
{:pending_async}
{:creates "CONSUMER"}
CONSUMER (x: int, {:linear_in "cid"} receive_handle: ChannelHandle)
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
    call create_async(CONSUMER(x'+1, receive_handle));
  }
  channels[cid] := Channel(C, head, tail);
  assume {:add_to_pool "INV2", channels[cid]} true;
}

////////////////////////////////////////////////////////////////////////////////

procedure {:IS_abstraction}{:layer 2}
{:creates "CONSUMER"}
CONSUMER' (x:int, {:linear_in "cid"} receive_handle: ChannelHandle)
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
  call CONSUMER(x, receive_handle);
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
