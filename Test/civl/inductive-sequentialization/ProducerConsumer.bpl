// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// FIFO channel
datatype Channel { Channel(C: [int]int, head: int, tail: int) }

// id of a FIFO channel
type ChannelId;

// permission for sending to or receiving from a channel
datatype {:linear "cid"} ChannelHandle { Send(cid: ChannelId), Receive(cid: ChannelId) }

function {:inline} {:linear "cid"} ChannelIdCollector(cid: ChannelId) : [ChannelHandle]bool {
  MapConst(false)[Send(cid) := true][Receive(cid) := true]
}

// pool of FIFO channels
var {:layer 0,3} channels: [ChannelId]Channel;

////////////////////////////////////////////////////////////////////////////////

>-< action {:layer 2} MAIN ({:linear_in "cid"} cid: ChannelId)
refines MAIN' using INV;
creates PRODUCER, CONSUMER;
eliminates CONSUMER using CONSUMER';
{
  assert channels[cid]->head == channels[cid]->tail;
  call create_async(PRODUCER(1, Send(cid)));
  call create_async(CONSUMER(1, Receive(cid)));
}

>-< action {:layer 3} MAIN' ({:linear_in "cid"} cid: ChannelId)
modifies channels;
{
  var channel: Channel;

  assert channels[cid]->head == channels[cid]->tail;
  assume channel->head == channel->tail;
  channels[cid] := channel;
}

invariant action {:layer 2}
INV ({:linear_in "cid"} cid: ChannelId)
creates PRODUCER, CONSUMER;
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

async <- action {:layer 2} PRODUCER (x: int, {:linear_in "cid"} send_handle: ChannelHandle)
creates PRODUCER;
modifies channels;
{
  var channel: Channel;
  var C: [int]int;
  var head, tail: int;

  assert send_handle is Send;
  channel := channels[send_handle->cid];
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
  channels[send_handle->cid] := Channel(C, head, tail);
  assume {:add_to_pool "INV2", channels[send_handle->cid]} true;
}

async action {:layer 2} CONSUMER (x: int, {:linear_in "cid"} receive_handle: ChannelHandle)
creates CONSUMER;
modifies channels;
{
  var channel: Channel;
  var C: [int]int;
  var head, tail: int;
  var x': int;

  assert receive_handle is Receive;
  channel := channels[receive_handle->cid];
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
  channels[receive_handle->cid] := Channel(C, head, tail);
  assume {:add_to_pool "INV2", channels[receive_handle->cid]} true;
}

////////////////////////////////////////////////////////////////////////////////

abstract action {:layer 2} CONSUMER' (x:int, {:linear_in "cid"} receive_handle: ChannelHandle)
creates CONSUMER;
modifies channels;
{
  var channel: Channel;
  var head, tail: int;

  channel := channels[receive_handle->cid];
  head := channel->head;
  tail := channel->tail;
  assert head < tail;
  call CONSUMER(x, receive_handle);
}

////////////////////////////////////////////////////////////////////////////////

yield procedure {:layer 1}
main ({:linear_in "cid"} cid: ChannelId)
refines MAIN;
{
  var {:linear "cid"} send_handle, receive_handle: ChannelHandle;

  call send_handle, receive_handle := split(cid);
  async call producer(1, send_handle);
  async call consumer(1, receive_handle);
}

yield procedure {:layer 1}
producer (x:int, {:linear_in "cid"} send_handle: ChannelHandle)
refines PRODUCER;
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

yield procedure {:layer 1}
consumer (x:int, {:linear_in "cid"} receive_handle: ChannelHandle)
refines CONSUMER;
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

>-< action {:layer 1} SEND (m: int, {:linear "cid"} send_handle: ChannelHandle)
modifies channels;
{
  var channel: Channel;
  var C: [int]int;
  var head, tail: int;

  assert send_handle is Send;
  channel := channels[send_handle->cid];
  C := channel->C;
  head := channel->head;
  tail := channel->tail;
  C[tail] := m;
  tail := tail + 1;
  channels[send_handle->cid] := Channel(C, head, tail);
}

>-< action {:layer 1} RECEIVE ({:linear "cid"} receive_handle: ChannelHandle) returns (m:int)
modifies channels;
{
  var channel: Channel;
  var C: [int]int;
  var head, tail: int;

  assert receive_handle is Receive;
  channel := channels[receive_handle->cid];
  C := channel->C;
  head := channel->head;
  tail := channel->tail;
  assume head < tail;
  m := C[head];
  head := head + 1;
  channels[receive_handle->cid] := Channel(C, head, tail);
}

<-> action {:layer 1} SPLIT({:linear_in "cid"} cid: ChannelId)
  returns ({:linear "cid"} send_handle: ChannelHandle, {:linear "cid"} receive_handle: ChannelHandle)
{
  send_handle := Send(cid);
  receive_handle := Receive(cid);
}

yield procedure {:layer 0} send (m: int, {:linear "cid"} send_handle: ChannelHandle);
refines SEND;

yield procedure {:layer 0} receive ({:linear "cid"} receive_handle: ChannelHandle) returns (m: int);
refines RECEIVE;

yield procedure {:layer 0} split({:linear_in "cid"} cid: ChannelId) returns ({:linear "cid"} send_handle: ChannelHandle, {:linear "cid"} receive_handle: ChannelHandle);
refines SPLIT;
