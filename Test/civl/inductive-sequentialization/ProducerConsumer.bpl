// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// FIFO channel
datatype Channel { Channel(C: [int]int, head: int, tail: int) }

// id of a FIFO channel
type ChannelId;

// permission for sending to or receiving from a channel
datatype ChannelHandle { Send(cid: ChannelId), Receive(cid: ChannelId) }

function {:inline} BothHandles(cid: ChannelId): Set ChannelHandle
{ Set_Add(Set_Singleton(Send(cid)), Receive(cid)) }

// pool of FIFO channels
var {:layer 0,1} channels: [ChannelId]Channel;

////////////////////////////////////////////////////////////////////////////////

yield invariant {:layer 1} YieldMain(cid: ChannelId, {:linear} handles: Set ChannelHandle);
invariant handles == BothHandles(cid);
invariant channels[cid]->head == 0;
invariant channels[cid]->tail == 0;

yield invariant {:layer 1} YieldProducer(x: int, {:linear} send_handle: One ChannelHandle);
invariant send_handle->val is Send;
invariant (var channel := channels[send_handle->val->cid]; x == channel->tail + 1);
invariant (var channel := channels[send_handle->val->cid];
          (var head, tail, C := channel->head, channel->tail, channel->C;
          (forall i: int:: head <= i && i < tail ==> C[i] == i + 1)));

yield invariant {:layer 1} YieldConsumer(x: int, {:linear} receive_handle: One ChannelHandle);
invariant receive_handle->val is Receive;
invariant (var channel := channels[receive_handle->val->cid]; x == channel->head + 1);
invariant (var channel := channels[receive_handle->val->cid];
          (var head, tail, C := channel->head, channel->tail, channel->C;
          (forall i: int:: head <= i && i < tail ==> C[i] == i + 1 || (i + 1 == tail && C[i] == 0))));

////////////////////////////////////////////////////////////////////////////////

yield procedure {:layer 1}
main (cid: ChannelId, {:linear_in} handles: Set ChannelHandle)
requires call YieldMain(cid, handles);
{
  var {:linear} handles': Set ChannelHandle;
  var {:linear} send_handle, receive_handle: One ChannelHandle;

  handles' := handles;
  call send_handle := One_Get(handles', Send(cid));
  call receive_handle := One_Get(handles', Receive(cid));
  async call producer(1, send_handle);
  async call consumer(1, receive_handle);
}

yield procedure {:layer 1}
producer (x: int, {:linear_in} send_handle: One ChannelHandle)
requires call YieldProducer(x, send_handle);
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
consumer (x: int, {:linear_in} receive_handle: One ChannelHandle)
requires call YieldConsumer(x, receive_handle);
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

atomic action {:layer 1} SEND (m: int, {:linear} send_handle: One ChannelHandle)
modifies channels;
{
  var channel: Channel;
  var C: [int]int;
  var head, tail: int;

  assert send_handle->val is Send;
  channel := channels[send_handle->val->cid];
  C := channel->C;
  head := channel->head;
  tail := channel->tail;
  C[tail] := m;
  tail := tail + 1;
  channels[send_handle->val->cid] := Channel(C, head, tail);
}

atomic action {:layer 1} RECEIVE ({:linear} receive_handle: One ChannelHandle) returns (m:int)
modifies channels;
{
  var channel: Channel;
  var C: [int]int;
  var head, tail: int;

  assert receive_handle->val is Receive;
  channel := channels[receive_handle->val->cid];
  C := channel->C;
  head := channel->head;
  tail := channel->tail;
  assume head < tail;
  m := C[head];
  head := head + 1;
  channels[receive_handle->val->cid] := Channel(C, head, tail);
}

yield procedure {:layer 0} send (m: int, {:linear} send_handle: One ChannelHandle);
refines SEND;

yield procedure {:layer 0} receive ({:linear} receive_handle: One ChannelHandle) returns (m: int);
refines RECEIVE;

