// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const n:int;
axiom n >= 1;

type val = int;
type {:linear "collect", "broadcast"} pid = int;

function {:inline} pid(i:int) : bool { 1 <= i && i <= n }

function {:inline} InitialBroadcastPAs (k:pid) : [BROADCAST]bool
{
  (lambda pa:BROADCAST :: pid(pa->i) && pa->i < k)
}

function {:inline} InitialCollectPAs (k:pid) : [COLLECT]bool
{
  (lambda pa:COLLECT :: pid(pa->i) && pa->i < k)
}

function {:inline} AllBroadcasts () : [BROADCAST]bool
{ (lambda pa:BROADCAST :: pid(pa->i)) }

function {:inline} AllCollects () : [COLLECT]bool
{ (lambda pa:COLLECT :: pid(pa->i)) }

function {:inline} RemainingBroadcasts (k:pid) : [BROADCAST]bool
{ (lambda {:pool "Broadcast"} pa:BROADCAST :: k < pa->i && pa->i <= n) }

function {:inline} RemainingCollects (k:pid) : [COLLECT]bool
{ (lambda {:pool "Collect"} pa:COLLECT :: k < pa->i && pa->i <= n) }

////////////////////////////////////////////////////////////////////////////////

var {:layer 0,1} CH_low:[pid][val]int;
var {:layer 1,4} CH:[val]int;
var {:layer 0,4} value:[pid]val;
var {:layer 0,4} decision:[pid]val;

function max(CH:[val]int) : val;
function card(CH:[val]int) : int;

axiom card(MultisetEmpty) == 0;
axiom (forall CH:[val]int, v:val, x:int :: card(CH[v := x]) == card(CH) + x - CH[v]);
axiom (forall m:[val]int, m':[val]int :: MultisetSubsetEq(m, m') && card(m) == card(m') ==> m == m');

axiom (forall v:val :: max(MultisetSingleton(v)) == v);
axiom (forall CH:[val]int, v:val, x:int :: x > 0 ==> max(CH[v := x]) == (if v > max(CH) then v else max(CH)));

function value_card(v:val, value:[pid]val, i:pid, j:pid) : int
{
  if j < i then
    0
  else
    if value[j] == v then
      value_card(v, value, i, j-1) + 1
    else
      value_card(v, value, i, j-1)
}

////////////////////////////////////////////////////////////////////////////////

// NOTE: Civl currently does not support variables to be linear in multiple
// domains (i.e., supplying multiple linear annotations). In the future we
// would like the MAIN action(s) to take a single parameter as follows:
//     {:linear_in "broadcast"}{:linear_in "collect"} pids:[pid]bool

>-< action {:layer 4}
MAIN''({:linear_in "broadcast"} pidsBroadcast:[pid]bool, {:linear_in "collect"} pidsCollect:[pid]bool)
modifies CH, decision;
{
  assert pidsBroadcast == (lambda i:pid :: pid(i)) && pidsCollect == pidsBroadcast;
  assert CH == MultisetEmpty;
  CH := (lambda v:val :: value_card(v, value, 1, n));
  assume card(CH) == n;
  assume MultisetSubsetEq(MultisetEmpty, CH);
  decision := (lambda i:pid :: if pid(i) then max(CH) else old(decision)[i]);
}

action {:layer 3}
INV_COLLECT_ELIM({:linear_in "broadcast"} pidsBroadcast:[pid]bool, {:linear_in "collect"} pidsCollect:[pid]bool)
creates COLLECT;
modifies CH, decision;
{
  var {:pool "INV_COLLECT"} k: int;

  assert pidsBroadcast == (lambda i:pid :: pid(i)) && pidsCollect == pidsBroadcast;
  assert CH == MultisetEmpty;

  CH := (lambda v:val :: value_card(v, value, 1, n));
  assume card(CH) == n;
  assume MultisetSubsetEq(MultisetEmpty, CH);

  assume
    {:add_to_pool "INV_COLLECT", k, k+1}
    {:add_to_pool "Collect", COLLECT(n)}
    0 <= k && k <= n;
  decision := (lambda i:pid :: if 1 <= i && i <= k then max(CH) else decision[i]);
  call create_asyncs(RemainingCollects(k));
  call set_choice(COLLECT(k+1));
}

////////////////////////////////////////////////////////////////////////////////

>-< action {:layer 3}
MAIN'({:linear_in "broadcast"} pidsBroadcast:[pid]bool, {:linear_in "collect"} pidsCollect:[pid]bool)
refines MAIN'' using INV_COLLECT_ELIM;
creates COLLECT;
eliminates COLLECT using COLLECT';
modifies CH;
{
  assert pidsBroadcast == (lambda i:pid :: pid(i)) && pidsCollect == pidsBroadcast;
  assert CH == MultisetEmpty;

  assume {:add_to_pool "INV_COLLECT", 0} true;
  CH := (lambda v:val :: value_card(v, value, 1, n));
  assume card(CH) == n;
  assume MultisetSubsetEq(MultisetEmpty, CH);
  call create_asyncs(AllCollects());
}

>-< action {:layer 2}
MAIN({:linear_in "broadcast"} pidsBroadcast:[pid]bool, {:linear_in "collect"} pidsCollect:[pid]bool)
refines MAIN' using INV_BROADCAST_ELIM;
creates BROADCAST, COLLECT;
{
  assert pidsBroadcast == (lambda i:pid :: pid(i)) && pidsCollect == pidsBroadcast;

  assume {:add_to_pool "INV_BROADCAST", 0} true;
  assert CH == MultisetEmpty;

  call create_asyncs(AllBroadcasts());
  call create_asyncs(AllCollects());
}

action {:layer 2}
INV_BROADCAST_ELIM({:linear_in "broadcast"} pidsBroadcast:[pid]bool, {:linear_in "collect"} pidsCollect:[pid]bool)
creates BROADCAST, COLLECT;
modifies CH;
{
  var {:pool "INV_BROADCAST"} k: int;

  assert pidsBroadcast == (lambda i:pid :: pid(i)) && pidsCollect == pidsBroadcast;
  assert CH == MultisetEmpty;

  assume
    {:add_to_pool "INV_BROADCAST", k, k+1}
    {:add_to_pool "Broadcast", BROADCAST(n)}
    0 <= k && k <= n;
  CH := (lambda v:val :: value_card(v, value, 1, k));
  assume card(CH) == k;
  assume MultisetSubsetEq(MultisetEmpty, CH);
  call create_asyncs(RemainingBroadcasts(k));
  call create_asyncs(AllCollects());
  call set_choice(BROADCAST(k+1));
}

async <- action {:layer 2} BROADCAST({:linear_in "broadcast"} i:pid)
modifies CH;
{
  assert pid(i);
  CH := CH[value[i] := CH[value[i]] + 1];
}

async >-< action {:layer 2,3} COLLECT({:linear_in "collect"} i:pid)
modifies decision;
{
  var received_values:[val]int;
  assert pid(i);
  assume card(received_values) == n;
  assume MultisetSubsetEq(MultisetEmpty, received_values);
  assume MultisetSubsetEq(received_values, CH);
  decision[i] := max(received_values);
}

action {:layer 3} COLLECT'({:linear_in "collect"} i:pid)
modifies decision;
{
  assert CH == (lambda v:val :: value_card(v, value, 1, n));
  assert card(CH) == n;
  assert MultisetSubsetEq(MultisetEmpty, CH);
  call COLLECT(i);
}

////////////////////////////////////////////////////////////////////////////////

yield invariant {:layer 1} YieldInv();
invariant Inv(CH_low, CH);

function {:inline} Inv(CH_low:[pid][val]int, CH:[val]int) : bool
{
  (forall i:pid :: MultisetSubsetEq(MultisetEmpty, CH_low[i]) && MultisetSubsetEq(CH_low[i], CH))
}

link action {:layer 1} intro (i:pid)
modifies CH;
{
  CH := CH[value[i] := CH[value[i]] + 1];
}

////////////////////////////////////////////////////////////////////////////////

link action {:layer 1} Snapshot() returns (snapshot:[pid][val]int)
{
  snapshot := CH_low;
}

yield invariant {:layer 1}
YieldInit({:linear "broadcast"} pidsBroadcast:[pid]bool, {:linear "collect"} pidsCollect:[pid]bool);
invariant pidsBroadcast == (lambda ii:pid :: pid(ii)) && pidsCollect == pidsBroadcast;
invariant (forall ii:pid :: CH_low[ii] == MultisetEmpty);
invariant CH == MultisetEmpty;

yield procedure {:layer 1}
Main({:linear_in "broadcast"} pidsBroadcast:[pid]bool, {:linear_in "collect"} pidsCollect:[pid]bool)
refines MAIN;
requires call YieldInit(pidsBroadcast, pidsCollect);
{
  var {:pending_async}{:layer 1} Broadcast_PAs:[BROADCAST]int;
  var {:pending_async}{:layer 1} Collect_PAs:[COLLECT]int;
  var i:pid;
  var {:linear "broadcast"} s:pid;
  var {:linear "collect"} r:pid;
  var {:linear "broadcast"} ss:[pid]bool;
  var {:linear "collect"} rr:[pid]bool;

  ss := pidsBroadcast;
  rr := pidsCollect;
  i := 1;
  while (i <= n)
  invariant {:layer 1} 1 <= i && i <= n + 1;
  invariant {:layer 1} ss == (lambda ii:pid :: pid(ii) && ii >= i) && ss == rr;
  invariant {:layer 1} Broadcast_PAs == ToMultiset(InitialBroadcastPAs(i));
  invariant {:layer 1} Collect_PAs == ToMultiset(InitialCollectPAs(i));
  {
    call s, r, ss, rr := linear_transfer(i, ss, rr);
    async call Broadcast(s);
    async call Collect(r);
    i := i + 1;
  }
  assert {:layer 1} Broadcast_PAs == ToMultiset(AllBroadcasts());
  assert {:layer 1} Collect_PAs == ToMultiset(AllCollects());
}

yield procedure {:layer 1} Broadcast({:linear_in "broadcast"} i:pid)
refines BROADCAST;
requires {:layer 1} pid(i);
{
  var j: pid;
  var v: val;
  var {:layer 1} old_CH_low: [pid][val]int;

  call old_CH_low := Snapshot();
  call v := get_value(i);
  j := 1;
  while (j <= n)
  invariant {:layer 1} 1 <= j && j <= n+1;
  invariant {:layer 1} CH_low == (lambda jj: pid :: (if pid(jj) && jj < j then MultisetPlus(old_CH_low[jj], MultisetSingleton(value[i])) else old_CH_low[jj]));
  {
    call send(v, j);
    j := j + 1;
  }
  call intro(i);
}

yield procedure {:layer 1}
Collect({:linear_in "collect"} i:pid)
refines COLLECT;
requires call YieldInv();
requires {:layer 1} pid(i);
{
  var j: pid;
  var d: val;
  var v: val;
  var {:layer 1} received_values: [val]int;
  var {:layer 1} old_CH_low: [pid][val]int;

  call old_CH_low := Snapshot();
  call d := receive(i);
  received_values := MultisetSingleton(d);
  j := 2;
  while (j <= n)
  invariant {:layer 1} 2 <= j && j <= n + 1;
  invariant {:layer 1} card(received_values) == j - 1;
  invariant {:layer 1} MultisetSubsetEq(MultisetEmpty, received_values);
  invariant {:layer 1} MultisetSubsetEq(received_values, old_CH_low[i]);
  invariant {:layer 1} CH_low == old_CH_low[i := MapSub(old_CH_low[i], received_values)];
  invariant {:layer 1} d == max(received_values);
  {
    call v := receive(i);
    if (v > d) { d := v; }
    received_values[v] := received_values[v] + 1;
    j := j + 1;
  }
  call set_decision(i, d);
}

////////////////////////////////////////////////////////////////////////////////

<-> action {:layer 1} GET_VALUE(i:pid) returns (v:val)
{
  v := value[i];
}

<-> action {:layer 1} SET_DECISION({:linear_in "collect"} i:pid, d:val)
modifies decision;
{
  decision[i] := d;
}

<- action {:layer 1} SEND(v:val, i:pid)
modifies CH_low;
{
  CH_low[i][v] := CH_low[i][v] + 1;
}

-> action {:layer 1} RECEIVE(i:pid) returns (v:val)
modifies CH_low;
{
  assume CH_low[i][v] > 0;
  CH_low[i][v] := CH_low[i][v] - 1;
}

<-> action {:layer 1}
LINEAR_TRANSFER(i:pid, {:linear_in "broadcast"} ss:[pid]bool, {:linear_in "collect"} rr:[pid]bool)
returns ({:linear "broadcast"} s:pid, {:linear "collect"} r:pid, {:linear "broadcast"} ss':[pid]bool, {:linear "collect"} rr':[pid]bool)
{
  assert ss[i] && rr[i];
  s, r := i, i;
  ss', rr' := ss[i := false], rr[i := false];
}

yield procedure {:layer 0} get_value(i:pid) returns (v:val);
refines GET_VALUE;

yield procedure {:layer 0} set_decision({:linear_in "collect"} i:pid, d:val);
refines SET_DECISION;

yield procedure {:layer 0} send(v:val, i:pid);
refines SEND;

yield procedure {:layer 0} receive(i:pid) returns (v:val);
refines RECEIVE;

yield procedure {:layer 0} linear_transfer(i:pid, {:linear_in "broadcast"} ss:[pid]bool, {:linear_in "collect"} rr:[pid]bool)
returns ({:linear "broadcast"} s:pid, {:linear "collect"} r:pid, {:linear "broadcast"} ss':[pid]bool, {:linear "collect"} rr':[pid]bool);
refines LINEAR_TRANSFER;

////////////////////////////////////////////////////////////////////////////////

const MultisetEmpty:[val]int;
axiom MultisetEmpty == MapConst(0);

function {:inline} MultisetSingleton(v:val) : [val]int
{
  MultisetEmpty[v := 1]
}

function {:inline} MultisetSubsetEq(a:[val]int, b:[val]int) : bool
{
  MapLe(a, b) == MapConst(true)
}

function {:inline} MultisetPlus(a:[val]int, b:[val]int) : [val]int
{
  MapAdd(a, b)
}

function {:inline} MultisetMinus(a:[val]int, b:[val]int) : [val]int
{
  MapSub(a, b)
}
