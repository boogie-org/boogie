// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype lockMsg {
  transfer(epoch:int),
  locked(epoch:int)
}

datatype msg { msg(src:int, dst:int, payload:lockMsg) }

datatype node { node(held:bool, epoch:int) }

// var network:set<msg>
var{:layer 1,2} network:[msg]bool;

// var external:set<msg>
var{:layer 1,3} external:[msg]bool;

// var nodes:imap<int, node>
var{:layer 1,2} nodes:[int]node;

datatype history { history(len:int, locks:[int]int) }

var{:layer 1,3} history:history;

function addHistory(h:history, l:int):history
{
  history(h->len + 1, h->locks[h->len := l])
}

function nextNode(me:int):int;


////// primitive actions //////

both action {:layer 2} AtomicGetNode({:linear} me: One int) returns(n:node)
{
        n := nodes[me->val];
}

yield procedure {:layer 1} GetNode({:linear} me: One int) returns(n:node);
refines AtomicGetNode;

both action {:layer 2} AtomicSetNode({:linear} me: One int, n:node)
modifies nodes;
{
        nodes := nodes[me->val := n];
}

yield procedure {:layer 1} SetNode({:linear} me: One int, n:node);
refines AtomicSetNode;

right action {:layer 2} AtomicRecv({:linear} me: One int) returns(m:msg)
{
        assume network[m] && m->dst == me->val;
}

yield procedure {:layer 1} Recv({:linear} me: One int) returns(m:msg);
refines AtomicRecv;

left action {:layer 2} AtomicSendInternal({:linear} me: One int, dst:int, payload:lockMsg)
modifies network;
{
        network := network[msg(me->val, dst, payload) := true];
}

yield procedure {:layer 1} SendInternal({:linear} me: One int, dst:int, payload:lockMsg);
refines AtomicSendInternal;

left action {:layer 2} AtomicSendExternal({:linear} me: One int, dst:int, payload:lockMsg)
modifies network, external;
{
        network  := network [msg(me->val, dst, payload) := true];
        external := external[msg(me->val, dst, payload) := true];
}

yield procedure {:layer 1} SendExternal({:linear} me: One int, dst:int, payload:lockMsg);
refines AtomicSendExternal;

atomic action {:layer 2} AtomicAddHistory(l:int)
modifies history;
{
        history  := addHistory(history, l);
}

yield procedure {:layer 1} AddHistory(l:int);
refines AtomicAddHistory;
////// composite actions //////

function EpochInHistory(epoch:int, history:history):bool
{
  0 <= epoch && epoch < history->len
}

function{:inline} IsFreshTransfer(network:[msg]bool, nodes:[int]node, m:msg):bool
{
  network[m] && m->payload is transfer && m->payload->epoch > nodes[m->dst]->epoch
}

function InvMsg(network:[msg]bool, nodes:[int]node, history:history, m:msg):bool
{
  m->payload is transfer ==>
      EpochInHistory(m->payload->epoch - 1, history)
   && m->dst == history->locks[m->payload->epoch - 1]
   && (IsFreshTransfer(network, nodes, m) ==> history->len == m->payload->epoch)
}

function InvNode(history:history, n:node):bool
{
  n->held ==> history->len == n->epoch
}

function Inv(network:[msg]bool, nodes:[int]node, history:history):bool
{
    0 <= history->len
&& (forall i:int :: InvNode(history, nodes[i]))
&& (forall i1:int, i2:int :: nodes[i1]->held && nodes[i2]->held ==> i1 == i2)
&& (forall i1:int, m2:msg :: nodes[i1]->held && IsFreshTransfer(network, nodes, m2) ==> false)
&& (forall m1:msg, m2:msg :: IsFreshTransfer(network, nodes, m1) && IsFreshTransfer(network, nodes, m2) ==> m1 == m2)
&& (forall m:msg :: network[m] ==> InvMsg(network, nodes, history, m))
}

atomic action {:layer 3} AtomicGrant({:linear} me: One int) returns(dst:int, epoch:int)
modifies history;
{
        history := addHistory(history, dst);
}

yield procedure {:layer 2}
Grant({:linear} me: One int) returns(dst:int, epoch:int)
refines AtomicGrant;
requires call YieldHeld(me);
preserves call YieldInv();
{
  var node:node;

  call node := GetNode(me);
  dst := nextNode(me->val);
  epoch := node->epoch;
  call AddHistory(dst);
  call SetNode(me, node(false, epoch));
  call SendInternal(me, dst, transfer(epoch + 1));
}

atomic action {:layer 3} AtomicAccept({:linear} me: One int, dst:int) returns(epoch:int)
modifies external;
{
        // specify that the message source (me) must appear at right epoch in history:
        assume EpochInHistory(epoch - 1, history);
        assume me->val == history->locks[epoch - 1];

        external := external[msg(me->val, dst, locked(epoch)) := true];
}

yield procedure {:layer 2}
Accept({:linear} me: One int, dst:int) returns(epoch:int)
refines AtomicAccept;
preserves call YieldInv();
{
  var node:node;
  var m:msg;

  while (true)
    invariant {:yields} true;
    invariant call YieldInv();
  {
    call m := Recv(me);
    call node := GetNode(me);
    epoch := m->payload->epoch;

    if (m->payload is transfer && epoch > node->epoch)
    {
      call SetNode(me, node(true, epoch));
      call SendExternal(me, dst, locked(epoch));
      return;
    }
  }
}

procedure CheckInitInv(network:[msg]bool, nodes:[int]node, history:history)
  requires network == (lambda m:msg :: false);
  requires nodes == (lambda i:int :: node(i == 0, if i == 0 then 1 else 0));
  requires history == history(1, (lambda i:int :: 0));
 ensures  Inv(network, nodes, history);
{
}

yield invariant {:layer 2} YieldInv();
invariant Inv(network, nodes, history);

yield invariant {:layer 2} YieldHeld({:linear} me: One int);
invariant nodes[me->val]->held;
